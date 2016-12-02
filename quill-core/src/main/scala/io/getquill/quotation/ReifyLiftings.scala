package io.getquill.quotation

import io.getquill.ast._
import scala.reflect.macros.whitebox.{ Context => MacroContext }
import scala.reflect.NameTransformer
import io.getquill.dsl.EncodingDsl
import io.getquill.norm.BetaReduction
import io.getquill.util.OptionalTypecheck
import io.getquill.util.Messages._

case class ScalarValueLifting[T, U](value: T, encoder: EncodingDsl#Encoder[U])
case class CaseClassValueLifting[T](value: T)

trait ReifyLiftings {
  val c: MacroContext
  import c.universe._

  private val liftings = TermName("liftings")

  private def encode(name: String) =
    TermName(NameTransformer.encode(name))

  private sealed trait Reified {
    val value: Tree
    val encoder: Tree
  }
  private case class ReifiedScalar(value: Tree, encoder: Tree) extends Reified
  private case class ReifiedCaseClass(value: Tree, encoder: Tree) extends Reified

  private case class ReifyLiftings(state: collection.Map[TermName, Reified])
    extends StatefulTransformer[collection.Map[TermName, Reified]] {

    private def reify(lift: Lift) =
      lift match {
        case ScalarValueLift(name, value: Tree, encoder: Tree)    => ReifiedScalar(value, encoder)
        case ScalarQueryLift(name, value: Tree, encoder: Tree)    => ReifiedScalar(value, encoder)
        case CaseClassValueLift(name, value: Tree, encoder: Tree) => ReifiedCaseClass(value, encoder)
        case CaseClassQueryLift(name, value: Tree, encoder: Tree) => ReifiedCaseClass(value, encoder)
      }

    override def apply(ast: Ast) =
      ast match {

        case ast: Lift =>
          (ast, ReifyLiftings(state + (encode(ast.name) -> reify(ast))))

        case Property(CaseClassValueLift(name, v: Tree, e: Tree), prop) =>
          val term = TermName(prop)
          val tpe = v.tpe.member(term).typeSignatureIn(v.tpe)
          val merge = c.typecheck(q"$v.$term")
          OptionalTypecheck(c)(q"implicitly[${c.prefix}.Encoder[$tpe]]") match {
            // TODO differentiate
            case enc => apply(ScalarValueLift(merge.toString, merge, enc))
            case enc =>
              tpe.baseType(c.symbolOf[Product]) match {
                case NoType => c.fail(s"Can't find an encoder for the lifted case class property '$merge'")
                case _      => apply(CaseClassValueLift(merge.toString, merge, enc))
              }
          }

        case QuotedReference(ref: Tree, refAst) =>
          val newAst =
            Transform(refAst) {
              case lift: Lift =>
                val nested =
                  q"$ref.$liftings.${encode(lift.name)}"
                lift match {
                  case ScalarValueLift(name, value, encoder) =>
                    ScalarValueLift(s"$ref.$name", q"$nested.value", q"$nested.encoder")
                  case CaseClassValueLift(name, value, encoder) =>
                    CaseClassValueLift(s"$ref.$name", q"$nested.value", q"$nested.encoder")
                  case ScalarQueryLift(name, value, encoder) =>
                    ScalarQueryLift(s"$ref.$name", q"$nested.value", q"$nested.encoder")
                  case CaseClassQueryLift(name, value, encoder) =>
                    CaseClassQueryLift(s"$ref.$name", q"$nested.value", q"$nested.encoder")
                }
            }
          apply(newAst)

        case other => super.apply(other)
      }
  }

  protected def reifyLiftings(ast: Ast): (Ast, Tree) =
    ReifyLiftings(collection.Map.empty)(ast) match {
      case (ast, _) =>
        // reify again with beta reduction, given that the first pass will remove `QuotedReference`s 
        ReifyLiftings(collection.Map.empty)(BetaReduction(ast)) match {
          case (ast, transformer) =>
            val trees =
              for ((name, reified) <- transformer.state) yield {
                reified match {
                  case ReifiedScalar(value, encoder) =>
                    q"val $name = io.getquill.quotation.ScalarValueLifting($value, $encoder)"
                  case ReifiedCaseClass(value, encoder) =>
                    q"val $name = io.getquill.quotation.CaseClassValueLifting($value, $encoder)"
                }
              }
            (ast, q"val $liftings = new { ..$trees }")
        }
    }
}
