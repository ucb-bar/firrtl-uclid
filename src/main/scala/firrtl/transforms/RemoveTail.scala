// See LICENSE for license details.

package firrtl
package transforms

import firrtl.ir._
import firrtl.Mappers._

import scala.collection.mutable

object RemoveTail {
  def removeTail(expr: Expression): Expression = expr.mapExpr(removeTail) match {
    case DoPrim(PrimOps.Tail, Seq(e), Seq(amt), tpe) =>
      val top = bitWidth(e.tpe) - amt
      DoPrim(PrimOps.Bits, Seq(e), Seq(top - 1, 0), tpe)
    case other => other
  }

  def removeTail(stmt: Statement): Statement = stmt.mapStmt(removeTail).mapExpr(removeTail)

  def removeTail(mod: DefModule): DefModule = mod.mapStmt(removeTail)
}

/** Remove tail operations from low firrtl */
class RemoveTail extends Transform {
  def inputForm = LowForm
  def outputForm = LowForm

  def execute(state: CircuitState): CircuitState = {
    val c = state.circuit.mapModule(RemoveTail.removeTail)
    state.copy(circuit = c)
  }
}
