package io.getquill.sql

import scala.reflect.ClassTag
import language.experimental.macros
import io.getquill.impl.Queryable
import io.getquill.impl.Quoted

abstract class SqlSource[R: ClassTag, S: ClassTag] extends io.getquill.impl.Source[R, S] {

  def run[T](q: Queryable[T]): Any = macro SqlQueryMacro.run[R, S, T]
  def run[P1, T](q: P1 => Queryable[T])(p1: P1): Any = macro SqlQueryMacro.run1[P1, R, S, T]
  def run[P1, P2, T](q: (P1, P2) => Queryable[T])(p1: P1, p2: P2): Any = macro SqlQueryMacro.run2[P1, P2, R, S, T]
  
  
}
