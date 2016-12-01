package io.getquill.idiom

import io.getquill.ast._

sealed trait Token

case class StringToken(string: String) extends Token {
  override def toString = string
}

case class ScalarLiftToken(lift: ScalarLift) extends Token {
  override def toString = s"lift(${lift.name})"
}

case class CaseClassLiftToken(lift: CaseClassLift) extends Token {
  override def toString = s"lift(${lift.name})"
}

case class Statement(tokens: List[Token]) extends Token {
  override def toString = tokens.mkString
}
