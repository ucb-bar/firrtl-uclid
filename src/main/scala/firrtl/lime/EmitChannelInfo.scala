// See LICENSE for license details.

package firrtl
package lime

import firrtl.ir._
import firrtl.Mappers._
import firrtl.graph._
import firrtl.passes.MemPortUtils
import firrtl.Utils._
import firrtl.analyses.InstanceGraph

import org.json4s.native.Serialization

import scala.collection.mutable
import scala.collection.immutable.ListMap

import java.io._

// This is mostly copied from DCE
object DependencyGraph {

  /** Based on LogicNode ins CheckCombLoops, currently kind of faking it */
  type LogicNode = MemoizedHash[WrappedExpression]
  object LogicNode {
    def apply(moduleName: String, expr: Expression): LogicNode =
      WrappedExpression(Utils.mergeRef(WRef(moduleName), expr))
    def apply(moduleName: String, name: String): LogicNode = apply(moduleName, WRef(name))
    /** External Modules are representated as a single node driven by all inputs and driving all
      * outputs
      */
    def apply(ext: ExtModule): LogicNode = LogicNode(ext.name, ext.name)

    // This feels sketchy
    def unapply(node: LogicNode): Option[(String, String)] = {
      val (mod, comp) = Utils.splitRef(node.t.e1)
      Some((mod.serialize, comp.serialize))
    }
  }

  /** Expression used to represent outputs in the circuit (# is illegal in names) */
  private val circuitSink = LogicNode("#Top", "#Sink")

  /** Extract all References and SubFields from a possibly nested Expression */
  private def extractRefs(expr: Expression): Seq[Expression] = {
    val refs = mutable.ArrayBuffer.empty[Expression]
    def rec(e: Expression): Expression = {
      e match {
        case ref @ (_: WRef | _: WSubField) => refs += ref
        case nested @ (_: Mux | _: DoPrim | _: ValidIf) => nested map rec
        case ignore @ (_: Literal) => // Do nothing
        case unexpected => throwInternalError()
      }
      e
    }
    rec(expr)
    refs
  }

  // Gets all dependencies and constructs LogicNodes from them
  private def getDepsImpl(mname: String,
                          instMap: collection.Map[String, String])
                         (expr: Expression): Seq[LogicNode] =
    extractRefs(expr).map { e =>
      if (kind(e) == InstanceKind) {
        val (inst, tail) = Utils.splitRef(e)
        LogicNode(instMap(inst.name), tail)
      } else {
        LogicNode(mname, e)
      }
    }


  /** Construct the dependency graph within this module */
  private def setupDepGraph(depGraph: MutableDiGraph[LogicNode],
                            instMap: collection.Map[String, String])
                           (mod: Module): Unit = {
    def getDeps(expr: Expression): Seq[LogicNode] = getDepsImpl(mod.name, instMap)(expr)

    def onStmt(stmt: Statement): Unit = stmt match {
      case DefRegister(_, name, _, clock, reset, init) =>
        val node = LogicNode(mod.name, name)
        depGraph.addVertex(node)
        Seq(clock, reset, init).flatMap(getDeps(_)).foreach(ref => depGraph.addPairWithEdge(node, ref))
      case DefNode(_, name, value) =>
        val node = LogicNode(mod.name, name)
        depGraph.addVertex(node)
        getDeps(value).foreach(ref => depGraph.addPairWithEdge(node, ref))
      case DefWire(_, name, _) =>
        depGraph.addVertex(LogicNode(mod.name, name))
      case mem: DefMemory =>
        // Treat DefMems as a node with outputs depending on the node and node depending on inputs
        // From perpsective of the module or instance, MALE expressions are inputs, FEMALE are outputs
        val memRef = WRef(mem.name, MemPortUtils.memType(mem), ExpKind, FEMALE)
        val exprs = Utils.create_exps(memRef).groupBy(Utils.gender(_))
        val sources = exprs.getOrElse(MALE, List.empty).flatMap(getDeps(_))
        val sinks = exprs.getOrElse(FEMALE, List.empty).flatMap(getDeps(_))
        val memNode = getDeps(memRef) match { case Seq(node) => node }
        depGraph.addVertex(memNode)
        sinks.foreach(sink => depGraph.addPairWithEdge(sink, memNode))
        sources.foreach(source => depGraph.addPairWithEdge(memNode, source))
      case Attach(_, exprs) => // Add edge between each expression
        exprs.flatMap(getDeps(_)).toSet.subsets(2).map(_.toList).foreach {
          case Seq(a, b) =>
            depGraph.addPairWithEdge(a, b)
            depGraph.addPairWithEdge(b, a)
        }
      case Connect(_, loc, expr) =>
        // This match enforces the low Firrtl requirement of expanded connections
        val node = getDeps(loc) match { case Seq(elt) => elt }
        getDeps(expr).foreach(ref => depGraph.addPairWithEdge(node, ref))
      // Simulation constructs are treated as top-level outputs
      case Stop(_,_, clk, en) =>
        Seq(clk, en).flatMap(getDeps(_)).foreach(ref => depGraph.addPairWithEdge(circuitSink, ref))
      case Print(_, _, args, clk, en) =>
        (args :+ clk :+ en).flatMap(getDeps(_)).foreach(ref => depGraph.addPairWithEdge(circuitSink, ref))
      case Block(stmts) => stmts.foreach(onStmt(_))
      case ignore @ (_: IsInvalid | _: WDefInstance | EmptyStmt) => // do nothing
      case other => throw new Exception(s"Unexpected Statement $other")
    }

    // Add all ports as vertices
    mod.ports.foreach {
      case Port(_, name, _, _: GroundType) => depGraph.addVertex(LogicNode(mod.name, name))
      case other => throwInternalError()
    }
    onStmt(mod.body)
  }

  // TODO Make immutable?
  private def createDependencyGraph(instMaps: collection.Map[String, collection.Map[String, String]],
                                    doTouchExtMods: Set[String],
                                    c: Circuit): MutableDiGraph[LogicNode] = {
    val depGraph = new MutableDiGraph[LogicNode]
    c.modules.foreach {
      case mod: Module => setupDepGraph(depGraph, instMaps(mod.name))(mod)
      case ext: ExtModule =>
        // Connect all inputs to all outputs
        val node = LogicNode(ext)
        // Don't touch external modules *unless* they are specifically marked as doTouch
        // Simply marking the extmodule itself is sufficient to prevent inputs from being removed
        if (!doTouchExtMods.contains(ext.name)) depGraph.addPairWithEdge(circuitSink, node)
        ext.ports.foreach {
          case Port(_, pname, _, AnalogType(_)) =>
            depGraph.addPairWithEdge(LogicNode(ext.name, pname), node)
            depGraph.addPairWithEdge(node, LogicNode(ext.name, pname))
          case Port(_, pname, Output, _) =>
            val portNode = LogicNode(ext.name, pname)
            depGraph.addPairWithEdge(portNode, node)
            // Also mark all outputs as circuit sinks (unless marked doTouch obviously)
            if (!doTouchExtMods.contains(ext.name)) depGraph.addPairWithEdge(circuitSink, portNode)
          case Port(_, pname, Input, _) => depGraph.addPairWithEdge(node, LogicNode(ext.name, pname))
        }
    }
    // Connect circuitSink to ALL top-level ports (we don't want to change the top-level interface)
    val topModule = c.modules.find(_.name == c.main).get
    val topOutputs = topModule.ports.foreach { port =>
      depGraph.addPairWithEdge(circuitSink, LogicNode(c.main, port.name))
    }

    depGraph
  }

  def createDependencyGraph(c: Circuit): DiGraph[LogicNode] = {
    // Copied from DCE
    val instMap = (new InstanceGraph(c)).graph.getEdgeMap.map { case (k, v) =>
      k.module -> v.map(i => i.name -> i.module).toMap
    }
    DiGraph(createDependencyGraph(instMap, Set.empty, c))
  }
}

/** Makes RHS of connections to registers be a ref to a node
  * This ensures there's no logic in the RHS of connections to registers
  */
class EmitChannelInfo extends Transform {
  def inputForm = LowForm
  def outputForm = LowForm
  import DependencyGraph._

  private val channelPrefix = "channels"
  private val ChannelRegex = s"""${channelPrefix}_([^\\W_]+)_(\\w+)""".r

  // JSON case classes
  case class ChannelsJson(inputs: Seq[InputChannel], outputs: Seq[OutputChannel])
  case class Field(name: String, width: Int)
  case class InputChannel(name: String, fields: Seq[Field])
  case class OutputChannel(name: String, fields: Seq[Field], dependencies: Seq[String])

  private def getChannelDeps(c: Circuit): ChannelsJson = {
    // Beats Tuple4
    case class ChannelPort(port: Port, channel: String, field: String, node: LogicNode)

    val depGraph = createDependencyGraph(c)

    val topMod = c.modules.find(_.name == c.main).get
    val cports = topMod.ports.collect { case p @ Port(_, ChannelRegex(_,_), _,_) => p }

    val cports2 = topMod.ports.collect {
      case p @ Port(_, ChannelRegex(c, f), _,_) if f != "ready" && f != "valid" =>
        ChannelPort(p, c, f, LogicNode(topMod.name, p.name))
    }
    val cportsMap = cports2.groupBy(_.channel)
    val nodesToChannel = cports2.map(c => c.node -> c.channel).toMap

    // For ordering ports
    val portIndex = cports2.zipWithIndex.map { case (p, i) => p.port.name -> i }.toMap
    // For ordering channels
    val channelIndex = cports2.zipWithIndex
                              .groupBy(_._1.channel)
                              .mapValues { case vs => vs.map(_._2).max }

    val cportsDep = cportsMap.mapValues { cps =>
      cps.flatMap(cp => depGraph.reachableFrom(cp.node).flatMap(nodesToChannel.get))
         .distinct
         .sortBy(channelIndex)
    }

    val channels = cportsMap.toSeq.sortBy(x => channelIndex(x._1))
      .map { case (cname, cps) =>
        val fields = cps.sortBy(x => portIndex(x.port.name))
                        .map(cp => Field(cp.field, bitWidth(cp.port.tpe).toInt))
        val deps = cportsDep(cname)
        cps.head.port.direction match {
          case Input =>
            assert(deps.isEmpty)
            InputChannel(cname, fields)
          case Output =>
            OutputChannel(cname, fields, deps)
        }
      }
    val inputs = channels.collect { case in: InputChannel => in }
    val outputs = channels.collect { case out: OutputChannel => out }
    assert(channels.size == (inputs.size + outputs.size))
    ChannelsJson(inputs, outputs)
  }

  def execute(state: CircuitState): CircuitState = {
    val td = state.annotations.collectFirst { case TargetDirAnnotation(value) => value }.get
    val result = getChannelDeps(state.circuit)
    val outFile = new File(td, s"${state.circuit.main}.channels.json")
    val outputWriter = new PrintWriter(outFile)
    implicit val formats = org.json4s.DefaultFormats
    outputWriter.write(Serialization.writePretty(result))
    outputWriter.close()
    state
  }
}
