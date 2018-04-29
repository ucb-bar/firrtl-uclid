// See LICENSE for license details.

package firrtl
package transforms

import firrtl.ir._
import firrtl.Utils.kind
import firrtl.Mappers._

object SimplifyRegUpdate {
  def onStmt(namespace: Namespace)(stmt: Statement): Statement = stmt.map(onStmt(namespace)) match {
    case Connect(info, lhs, rhs) if kind(lhs) == RegKind =>
      val node = DefNode(info, namespace.newName(s"${lhs.serialize}_next"), rhs)
      val connect = Connect(info, lhs, WRef(node.name))
      Block(Seq(node, connect))
    case other => other
  }
  def onModule(mod: DefModule): DefModule = {
    val namespace = Namespace(mod)
    mod.map(onStmt(namespace))
  }
}

/** Makes RHS of connections to registers be a ref to a node
  * This ensures there's no logic in the RHS of connections to registers
  */
class SimplifyRegUpdate extends Transform {
  def inputForm = LowForm
  def outputForm = LowForm

  def execute(state: CircuitState): CircuitState = {
    val c = state.circuit.map(SimplifyRegUpdate.onModule)
    state.copy(circuit = c)
  }
}
