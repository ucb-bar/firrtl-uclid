// See LICENSE for license details.

package firrtl

import com.typesafe.scalalogging.LazyLogging
import java.nio.file.{Paths, Files}
import java.io.{Reader, Writer}

import scala.collection.mutable
import scala.sys.process._
import scala.io.Source

import firrtl.ir._
import firrtl.passes._
import firrtl.transforms._
import firrtl.annotations._
import firrtl.Mappers._
import firrtl.PrimOps._
import firrtl.WrappedExpression._
import firrtl.Utils._
import MemPortUtils.{memPortField, memType}
// Datastructures
import scala.collection.mutable.{ArrayBuffer, LinkedHashMap, HashSet}

class IndentLevel {
  var value: Int = 0
  def increase() = value += 2
  def decrease() = value -= 2
}

class UclidEmitter extends SeqTransform with Emitter {
  def inputForm = LowForm
  def outputForm = LowForm

  private def memAddrType(mem: DefMemory): UIntType = UIntType(IntWidth(ceilLog2(mem.depth) max 1))

  private def serialize_rhs_ref(wr: WRef)(implicit rhsPrimes: Boolean): String = {
    if (rhsPrimes) s"${wr.name}'" else s"${wr.name}"
  }

  private def serialize_unop(p: DoPrim, arg0: String): String = p.op match {
    case Neg => s"-$arg0"
    // TODO: fix big hack that assumes all 1-bit UInts are booleans
    case Not => if (get_width(p.tpe) == 1) s"!${arg0}" else s"~$arg0"
    case _ => throwInternalError(s"Illegal unary operator: ${p.op}")
  }

  private def serialize_binop(p: DoPrim, arg0: String, arg1: String): String = p.op match {
    case Add => s"(0bv1 ++ $arg0) + (0bv1 ++ $arg1)"
    case Sub => s"(0bv1 ++ $arg0) - (0bv1 ++ $arg1)"
    case Lt => s"$arg0 < $arg1"
    case Leq => s"$arg0 <= $arg1"
    case Gt => s"$arg0 > $arg1"
    case Geq => s"$arg0 >= $arg1"
    case Eq => s"$arg0 == $arg1"
    case Neq => s"$arg0 != $arg1"
    case And =>
      // TODO: fix big hack that assumes all 1-bit UInts are booleans
      if (get_width(p.tpe) == 1)
        s"$arg0 && $arg1"
      else
        s"$arg0 & $arg1"
    case Or =>
      // TODO: fix big hack that assumes all 1-bit UInts are booleans
      if (get_width(p.tpe) == 1)
        s"$arg0 || $arg1"
      else
        s"$arg0 | $arg1"
    case Xor => s"$arg0 ^ $arg1"
    case Bits => s"${arg0}[${arg1}]"
    case Cat => s"${arg0} ++ ${arg1}"
    case Pad =>
      val extra_bits = p.consts(0) - get_width(p.args(0).tpe)
      if (extra_bits > 0) 
        s"0bv${extra_bits} ++ ${arg0}"
      else
        s"${arg0}"
    case _ => throwInternalError(s"Illegal binary operator: ${p.op}")
  }

  private def serialize_ternop(p: DoPrim, arg0: String, arg1: String, arg2: String): String = p.op match {
    case Bits => s"${arg0}[${arg1}:${arg2}]"
    case _ => throwInternalError(s"Illegal ternary operator: ${p.op}")
  }

  private def serialize_prim(p: DoPrim)(implicit rhsPrimes: Boolean): String = (p.args.length, p.consts.length) match {
    case (2, 0) => serialize_binop(p, serialize_rhs_exp(p.args(0)), serialize_rhs_exp(p.args(1)))
    case (1, 0) => serialize_unop(p, serialize_rhs_exp(p.args(0)))
    case (1, 2) => serialize_ternop(p, serialize_rhs_exp(p.args(0)), p.consts(0).toString, p.consts(1).toString)
    case (1, 1) => serialize_binop(p, serialize_rhs_exp(p.args(0)), p.consts(0).toString)
    case (0, 2) => serialize_binop(p, p.consts(0).toString, p.consts(1).toString)
    case (0, 1) => serialize_unop(p, p.consts(0).toString)
    case _ => throwInternalError(s"Illegal primitive operator operands")
  }

  private def serialize_mux(m: Mux)(implicit rhsPrimes: Boolean): String = {
    val i = serialize_rhs_exp(m.cond)
    val t = serialize_rhs_exp(m.tval)
    val e = serialize_rhs_exp(m.fval)
    s"if ($i) then ($t) else ($e)"
  }

  private def get_width(w: Width): Int = w match {
    case IntWidth(iw: BigInt) => iw.intValue
    case _ => throwInternalError(s"Types must have integral widths")
  }

  private def get_width(tpe: Type): Int = tpe match {
    case UIntType(w: Width) => get_width(w)
    case SIntType(w: Width) => get_width(w)
    case _ => throwInternalError(s"Cannot get width of type ${tpe}")
  }

  private def serialize_rhs_exp(e: Expression)(implicit rhsPrimes: Boolean): String = e match {
    case wr: WRef => serialize_rhs_ref(wr)
    case ws: WSubField => serialize_rhs_ref(WRef(LowerTypes.loweredName(ws)))
    case m: Mux => serialize_mux(m)
    case p: DoPrim => serialize_prim(p)
    case ul: UIntLiteral => get_width(ul.width) match {
      // TODO: fix big hack that assumes all 1-bit UInts are booleans
      case 1 => if (ul.value == 1) "true" else "false"
      case i: Int =>
        s"${ul.value}bv${i}"
    }
    case _ => throwInternalError(s"Trying to emit unsupported expression")
  }

  private def serialize_lhs_exp(e: Expression): String = e match {
    case wr: WRef => wr.name
    case sub: WSubField => LowerTypes.loweredName(sub)
    case _ => throwInternalError(s"Trying to emit unsupported expression")
  }

  private def serialize_type(tpe: Type): String = tpe match {
    case UIntType(w: Width) => get_width(w) match {
      // TODO: fix big hack that assumes all 1-bit UInts are booleans
      case 1 => "boolean"
      case i: Int => s"bv${i}"
    }
    case SIntType(w: Width) => s"bv${get_width(w)}"
    case t => throwInternalError(s"Trying to emit unsupported type: ${t.serialize}")
  }

  private def indent_line()(implicit w: Writer, indent: IndentLevel): Unit = {
    w write (" " * indent.value)
  }

  private def emit_comment(s: String)(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line();
    w write s"// ${s}\n"
  }

  private def emit_port(p: Port)(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line()
    val dir = if (p.direction == Input) "input" else "output"
    val uclType = serialize_type(p.tpe)
    w write s"${dir} ${p.name} : ${uclType};\n"
  }

  private def emit_reg_decl(r: DefRegister)(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line()
    val uclType = serialize_type(r.tpe)
    w write s"var ${r.name} : ${uclType};\n"
  }

  private def emit_mem_decl(m: DefMemory)(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line()
    val uclType = serialize_type(m.dataType)
    val addrType = serialize_type(memAddrType(m))
    w write s"var ${m.name} : [$addrType]${uclType};\n"
  }

  private def emit_node_decl(r: DefNode)(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line()
    val uclType = serialize_type(r.value.tpe)
    w write s"var ${r.name} : ${uclType};\n"
  }

  private def emit_wire_decl(wire: DefWire)(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line()
    val uclType = serialize_type(wire.tpe)
    w write s"var ${wire.name} : ${uclType};\n"
  }

  private def emit_init(mems: Seq[DefMemory])(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line()
    w.write(s"init {\n")
    indent.increase()
    for (m <- mems) {
      indent_line()
      val addrType = serialize_type(memAddrType(m))
      val dataType = serialize_type(m.dataType)
      w.write(s"assume (forall (a : $addrType) :: ${m.name}[a] == 0$dataType);\n")
    }
    indent.decrease()
    indent_line()
    w.write("}\n")
  }

  private def emit_node_assignment(n: DefNode)(implicit w: Writer, indent: IndentLevel, rhsPrime: Boolean): Unit = {
    indent_line()
    w write s"${n.name}' = "
    w write serialize_rhs_exp(n.value)
    w write ";\n"
  }

  private def emit_connect(c: Connect)(implicit w: Writer, indent: IndentLevel, rhsPrime: Boolean): Unit = {
    val lhs = serialize_lhs_exp(c.loc)
    indent_line()
    w write s"${lhs}' = "
    w write serialize_rhs_exp(c.expr)
    w write ";\n"
  }

  private def emit_mem_reads(m: DefMemory)(implicit w: Writer, indent: IndentLevel, rhsPrime: Boolean): Unit = {
    for (r <- m.readers) {
      val lhs = serialize_lhs_exp(memPortField(m, r, "data"))
      val rref = serialize_rhs_exp(WRef(m.name))
      val ridx = serialize_rhs_exp(memPortField(m, r, "addr"))
      indent_line()
      w write s"${lhs}' = $rref[$ridx]"
      w write ";\n"
    }
  }

  private def writeProcedureName(m: DefMemory): String = s"write_mem_${m.name}"

  private case class WritePort(name: String, addr: String, data: String, en: String, mask: String)
  private def emit_mem_write_procedure(m: DefMemory)(implicit w: Writer, indent: IndentLevel, rhsPrime: Boolean): Unit = {
    indent_line()
    val pname = writeProcedureName(m)
    w.write(s"procedure $pname() modifies ${m.name}, havoc_${m.name};\n")
    indent_line()
    w.write("{\n")
    val ports = m.writers.map { wr =>
      val en = serialize_lhs_exp(memPortField(m, wr, "en"))
      val mask = serialize_lhs_exp(memPortField(m, wr, "mask"))
      val addr = serialize_lhs_exp(memPortField(m, wr, "addr"))
      val data = serialize_lhs_exp(memPortField(m, wr, "data"))
      WritePort(wr, addr, data, en, mask)
    }
    indent.increase()
    for (p <- ports) {
      indent_line()
      w.write(s"if (${p.en} && ${p.mask}) {\n")
      indent.increase()
      indent_line()
      w.write(s"${m.name}[${p.addr}] = ${p.data};\n")
      indent.decrease()
      indent_line()
      w.write("}\n")
    }
    // Check for address collisions
    for (Seq(p1, p2) <- ports.combinations(2)) {
      indent_line()
      w.write(s"if (${p1.en} && ${p2.en} && ${p1.mask} && ${p2.mask} && (${p1.addr} == ${p2.addr})) {\n")
      indent.increase()
      indent_line()
      w.write(s"havoc havoc_${m.name};\n")
      indent_line()
      w.write(s"${m.name}[${p1.addr}] = havoc_${m.name};\n")
      indent.decrease()
      indent_line()
      w.write("}\n")
    }
    indent.decrease()
    indent_line()
    w.write("}\n");
  }

  private def emit_mem_writes(m: DefMemory)(implicit w: Writer, indent: IndentLevel, rhsPrime: Boolean): Unit = {
    indent_line()
    val pname = writeProcedureName(m)
    w.write(s"call $pname();\n")
  }

  private def emit_open_module_scope(m: Module)(implicit w: Writer, indent: IndentLevel): Unit = {
    w write s"module ${m.name} {\n"
    indent.increase()
  }

  private def emit_open_next_scope()(implicit w: Writer, indent: IndentLevel): Unit = {
    indent_line()
    w write s"next {\n"
    indent.increase()
  }

  private def emit_close_scope()(implicit w: Writer, indent: IndentLevel): Unit = {
    indent.decrease()
    indent_line()
    w write s"}\n"
  }

  private def emit_module(m: Module)(implicit w: Writer): Unit = {
    // Just IO, nodes, registers
    val nodes = ArrayBuffer[DefNode]()
    val wire_decls = ArrayBuffer[DefWire]()
    val output_decls = m.ports.filter(_.direction == Output).map(p => p.name -> p).toMap
    val clocks = HashSet[Expression]()
    val reg_resets = HashSet[String]()
    val reg_decls = LinkedHashMap[String, DefRegister]()
    val mem_decls = ArrayBuffer[DefMemory]()
    val reg_assigns = ArrayBuffer[Connect]()
    val comb_assigns = ArrayBuffer[Connect]()
    val wire_assigns = ArrayBuffer[Connect]()
    def processStatements(s: Statement): Statement = s map processStatements match {
      case sx: DefNode =>
        nodes += sx
        sx
      case sx: DefRegister =>
        clocks += sx.clock
        sx.reset match {
          case wr: WRef =>
            reg_resets += wr.name
          case UIntLiteral(v: BigInt, _) if (v == 0) =>
          case _ => throwInternalError(s"Illegal reset signal ${sx.reset}")
        }
        reg_decls += sx.name -> sx
        sx
      case sx @ Connect(_, lhs, rhs) => kind(lhs) match {
          case RegKind => reg_assigns += sx
          case PortKind => comb_assigns += sx
          case MemKind => rhs.tpe match {
            case ClockType =>
              clocks += rhs
            case _ =>
              comb_assigns += sx
            }
          case _ =>
            throwInternalError(s"Only outputs, registers, and mem fields may be the lhs of Connect")
        }
        sx
      case sx @ DefMemory(_, n, dt, _, wlat, rlat, rs , ws, rws, _) =>
        require(wlat == 1 && rlat == 0 && rws.size == 0, "Must run after VerilogMemDelays!")
        require(dt.isInstanceOf[GroundType], "Must run after LowerTypes")
        mem_decls += sx
        wire_decls += DefWire(NoInfo, s"havoc_$n", dt)
        for (r <- rs) {
          val data = memPortField(sx, r, "data")
          val addr = memPortField(sx, r, "addr")
          val en = memPortField(sx, r, "en")
          wire_decls += DefWire(NoInfo, LowerTypes.loweredName(data), data.tpe)
          wire_decls += DefWire(NoInfo, LowerTypes.loweredName(addr), addr.tpe)
          wire_decls += DefWire(NoInfo, LowerTypes.loweredName(en), en.tpe)
        }
        for (w <- ws) {
          val data = memPortField(sx, w, "data")
          val addr = memPortField(sx, w, "addr")
          val en = memPortField(sx, w, "en")
          val mask = memPortField(sx, w, "mask")
          wire_decls += DefWire(NoInfo, LowerTypes.loweredName(data), data.tpe)
          wire_decls += DefWire(NoInfo, LowerTypes.loweredName(addr), addr.tpe)
          wire_decls += DefWire(NoInfo, LowerTypes.loweredName(en), en.tpe)
          wire_decls += DefWire(NoInfo, LowerTypes.loweredName(mask), mask.tpe)
        }
        sx
      case Connect(_,_,_) | DefWire(_,_,_) | WDefInstance(_,_,_,_) =>
        // These are illegal for now
        throw EmitterException("Using illegal statement!")
      case sx =>
        sx
    }
    processStatements(m.body)
    // Consistency checks to see if module uses <=1 clock and <=1 reset
    if (clocks.size > 1 || reg_resets.size > 0)
      throw EmitterException("Uclid backend supports only a single clock and zero explicit resets")
    implicit val indent = new IndentLevel()
    emit_open_module_scope(m)
    m.ports.filter(p => p.tpe != ClockType && !reg_resets.contains(p.name)).foreach(emit_port(_))
    emit_comment("Registers")
    reg_decls.foreach({ case (k, v) => emit_reg_decl(v) })
    emit_comment("Memories")
    mem_decls.foreach(emit_mem_decl(_))
    emit_comment("Wires")
    wire_decls.foreach(emit_wire_decl(_))
    emit_comment("Nodes")
    nodes.foreach(emit_node_decl(_))
    emit_comment("Init")
    emit_init(mem_decls)
    implicit var rhsPrimes = false
    emit_comment("Mem Writes")
    mem_decls.foreach(emit_mem_write_procedure(_))
    emit_open_next_scope()
    emit_comment("Clock High")
    mem_decls.foreach(emit_mem_writes(_))
    reg_assigns.foreach(emit_connect(_))
    rhsPrimes = true
    emit_comment("Clock Low")
    nodes.foreach(emit_node_assignment(_))
    mem_decls.foreach(emit_mem_reads(_))
    comb_assigns.foreach(emit_connect(_))
    emit_close_scope()
    emit_close_scope()
  }

  def emit(cs: CircuitState, w: Writer): Unit = {
    val circuit = runTransforms(cs).circuit
    assert(circuit.modules.length == 1) // flat circuits, for now
    circuit.modules.head match {
      case m: Module => emit_module(m)(w)
      case _ => throw EmitterException(s"UCLID backed supports ordinary modules only!")
    }
  }

  /** Transforms to run before emission */
  def transforms = Seq(
    new RemoveTail,
    new SimplifyRegUpdate,
    new lime.EmitChannelInfo
  )

  override def execute(cs: CircuitState): CircuitState = {
    val extraAnnotations = cs.annotations.flatMap {
      case EmitCircuitAnnotation(_) =>
        val writer = new java.io.StringWriter
        emit(cs, writer)
        Seq(EmittedVerilogCircuitAnnotation(EmittedVerilogCircuit(cs.circuit.main, writer.toString)))
      case _ => Seq()
    }
    cs.copy(annotations = extraAnnotations ++ cs.annotations)
  }
}
