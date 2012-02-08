import java.io._
import scala.io._
import cs162.notScheme.syntax._
import scala.collection.mutable.{Map => MMap}
//kenneth hwang
//john meeker
object notScheme {
  import cs162.notScheme.interpreter._
  import SemanticHelpers._
  import Interp._

  def main(args:Array[String]) {
    val ast = ParseL.getAST(Source.fromFile(args(0)).mkString)

    if (args.length == 1 || args(1) != "--printast") 
      eval(inject(ast))
    else 
      PrettyPrint.writeDot(ast, "ast.dot")
  }
}

package cs162.notScheme.interpreter {
  case class Config(t:Term, env:Env)
 
  case class Env(env:Map[Var, Address] = Map()) {
    def apply(x:Var): Address = {
      env get x match {
        case Some(a) => a
        case None => { 
            throw undefined("free variable")
          }

      }
    }
    def +(tup:Tuple2[Var, Address]): Env = Env(env + tup)
  }

  case class Store(store:MMap[Address, Value] = MMap()) {
    def apply(a:Address): Value = {
      store get a match {
        case Some(v) => v
        case None => throw undefined("non-existent address")
      }
    }
  }

 
  sealed abstract class Value
  case class NumV(n:BigInt) extends Value { 
    override def toString = n.toString 
  }
  case class BoolV(b:Boolean) extends Value { 
    override def toString = b.toString 
  }
  case class StringV(str:String) extends Value { 
    override def toString = str
  }
  sealed abstract class ListV extends Value
  case class Empty() extends ListV
  case class ListF(v:Value, a:Address) extends ListV
  case class Address(a:Int) extends Value
  case class FunClo(env:Env, fun:Fun) extends Value {
    override def toString = "<closure>" 
  }
  case class UnitV() extends Value { 
    override def toString = "unit" 
  }
  object Env { 
    implicit def env2map(e:Env): Map[Var, Address] = e.env
    implicit def map2env(m:Map[Var, Address]): Env = Env(m)
  }
  object Store { 
    implicit def store2map(s:Store): MMap[Address, Value] = s.store
    implicit def map2store(m:MMap[Address, Value]): Store = Store(m)
  }
  object Address { 
    var id = 0
    def apply(): Address = { id += 1; Address(id) }
  }
 
 
  case class undefined(msg:String) extends Exception(msg)
 
  object SemanticHelpers {
    import Interp._
 
 
    def inject(prog:Program): Config = {
 
      return Config(prog.t,Env())
    }
 
    def alloc(v:Value): Address = {
      val a = Address()
      gStore(a) = v
      a
    }
 
    def makeList(vs:List[Value]): Address = {
 
      def makeCell(v:Value, a:Address): Address = alloc( ListF(v, a) )
      vs.foldRight( alloc(Empty()) ) (makeCell)
    }
		
 


  }
 
  object Interp {
    import SemanticHelpers._
    def l_print(lv:Value): Value = {
      lv match {
        case ListF(v, a) => {
            print(v)
            gStore(a) match {
              case Empty() => UnitV()
              case _ => {
                  print(", ")
                  l_print( gStore(a) )
                }
            }
          }
        case _ => UnitV()
      }
    }
    val gStore = Store()
    def eval(config:Config): Value = {
      val env = config.env
 
      def evalTo(t:Term): Value = t match {
        case Seq(t1, t2) => {
            evalTo(t1)
            evalTo(t2)
          }
        case Assign(x, e) => {
            gStore(env(x)) = evalTo(e)
            UnitV()
          }
        case w @ While(e, t) => evalTo(e) match {
            case BoolV(true) => {
                evalTo(t)
                evalTo(w)
              }
            case BoolV(false) => UnitV()
            case _ => throw undefined("while guard not a bool")
          }
        case Out(e) => evalTo(e) match {
            
            case Address(a) => {
                val list = gStore(Address(a))
                list match {
                  case ListF(v, a) => {
                      print("[")
                      l_print( list )
                      println("]")
                      UnitV()
                    }
                  case Empty() => {
                      println("[]")
                      UnitV()
                    }
                  case _ => {
                      println(evalTo(e)) 
                      UnitV()
                    }
                }
              }
            case _ => { println(evalTo(e)) }
              UnitV()
          }
        case HAssign(e1, e2) => e1 match {
 
            case x:Var => gStore(env(x)) match {
                case Address(a) => {
                    gStore(Address(a)) match {
                      case ListF(v, a2) => {
                          gStore(Address(a)) = ListF(evalTo(e2), a2)
                          UnitV()
                        }
                      case Empty() => throw undefined("assigning to head of empty list")
                      case _ => throw undefined("taking the head of a non-list")
                    }
                  }
                case _ => throw undefined("assigning to head of a non-list")
              }
            case _ => throw undefined("assigning to head of a non-list")
          }
        case TAssign(e1, e2) => e1 match {
 
            case x:Var => gStore(env(x)) match {
                case Address(a) => {
                    gStore(Address(a)) match {
                      case ListF(v, a2) => {
                          evalTo(e2) match {
                            case Address(a3) => {
                                gStore(Address(a)) = ListF(v, Address(a3))
                                UnitV()
                              }
                            case Empty() => throw undefined("assigning to tail of empty list")
                            case _ => throw undefined("bad tail assignment")
                          }
                        }
                      case Empty() => throw undefined("assigning to tail of empty list")
                      case _ => throw undefined("bad tail assignment")
                    }
                  }
                case _ => throw undefined("bad tail assignment")
              }
            case _ => throw undefined("bad tail assignment")
          }
        case Num(n) => NumV(n)
        case Bool(b) => BoolV(b)
        case Str(str) => StringV(str)
        case NotUnit() => UnitV()
        case x:Var => gStore(env(x))
        case Not(e) => evalTo(e) match {
            case BoolV(b) => BoolV(!b)
            case _ => throw undefined("negated expression not a bool")
          }
        case BinOp(bop, e1, e2) => bop match {
            case Equal => {
                (evalTo(e1), evalTo(e2)) match {
                  case (Address(a1), Address(a2)) => {
                      (gStore(Address(a1)), gStore(Address(a2))) match {
                        case (Empty(), Empty()) => {
                            BoolV(true)
                          }
                        case (ListF(v3,a3), ListF(v4,a4)) => {
                            BoolV(a1 == a2)
                          }
                        case _ => {
                            BoolV(evalTo(e1) == evalTo(e2))
                          }
                      }
                    }
                  case _ => {
                      BoolV(evalTo(e1) == evalTo(e2))
                    }
                }
              }
            case _ => (evalTo(e1), evalTo(e2)) match {
                case (BoolV(b1), BoolV(b2)) => bop match {
                    case And => BoolV(b1 && b2)
                    case Or => BoolV(b1 || b2)
                    case _ => throw undefined("illegal operation on bools")
                  }
                case (NumV(n1), NumV(n2)) => bop match {
                    case Add => NumV(n1 + n2)
                    case Sub => NumV(n1 - n2)
                    case Mul => NumV(n1 * n2)
                    case Div if n2 != 0 => NumV(n1 / n2)
                    case Lte => BoolV(n1 <= n2)
                    case _ => throw undefined("illegal operation on nums")
                  }
                case (StringV(s1), StringV(s2)) => bop match {
                    case Add => StringV(s1 + s2)
                    case Lte => BoolV(s1 <= s2)
                    case _ => throw undefined("illegal operation on strings")
                  }
						
                case (v:Value, a:Address) => bop match {
                    case Cons => {
								
                        val v2 = gStore(a)
                        v2 match {
                          case ListF(v1, a1) => {
                              val listhingy = makeList(List(v))
                              gStore(listhingy) match {
                                case ListF(v3, a3) => {
                                    gStore(a3) = v2
                                  }
                                case _ => throw undefined("expected ListF!")
                              }
                              return listhingy
                            }
                          case Empty() => {
                              makeList(List(v))
                            }
                          case _ => {
                              makeList(List(v, v2))
                            }
                        }
								
                      }
                    case _ => throw undefined("illegal operation on lists")
                  }
						
                case _ => throw undefined("illegal binary operation")
              }
          }
        case If(e, t1, t2) => evalTo(e) match {
            case BoolV(true) => evalTo(t1)
            case BoolV(false) => evalTo(t2)
            case _ => throw undefined("if guard not a bool")
          }
        case In(typ) => typ match {
            case NumT => NumV(BigInt(scala.Console.readLine()))
            case StrT => StringV(scala.Console.readLine())
          }
        case Call(ef, es) => {
 
            evalTo(ef) match {
              case (FunClo(e, f)) => {
                  if(es.length != f.xs.length) throw undefined("arguments and parameters don't match")
                  else{
                    (f.xs zip es).map( zz => { gStore(e(zz._1)) = evalTo(zz._2) } ) 
                    ef match {
                      case Var(x) => {
                          eval(Config(f.t, Env(e.env+( f.f -> env(Var(x))) )))
                        }
                      case _ => throw undefined("expected Var")
                    }
                  }
                } 
              case _ => throw undefined("expected FunClo")
            }
          }
        case NotList(es) => {
            makeList( (es map evalTo) )
          }
        case Head(e) => evalTo(e) match {
            case Address(a) => {
                gStore(Address(a)) match {
                  case ListF(v, a) => v
                  case Empty() => throw undefined("taking the head of an empty list")
                  case _ => throw undefined("taking the head of a non-list")
                }
              }
            case Empty() => throw undefined("taking the head of an empty list")
            case _ => throw undefined("taking the head of a non-list")
          }
        case Tail(e) => evalTo(e) match {
 
            case Address(a) => {
                gStore(Address(a)) match {
                  case ListF(v, a) => alloc(gStore(a))
                  case Empty() => throw undefined("taking the tail of an empty list")
                  case _ => throw undefined("taking the tail of a non-list")
                }
              }
            case Empty() => throw undefined("taking the tail of an empty list")
            case _ => throw undefined("taking the tail of a non-list")
          }
        case Block(vbs, t) => {
					
            val newenv = (for ( VarBind(x, e) <- vbs ) yield (x, UnitV()) ).foldLeft( env )( (env, xv) => env + (xv._1 -> alloc(xv._2)) )
            (for ( VarBind(x, e) <- vbs ) yield (x, evalTo(e))).foldLeft()( (a, xv) => gStore(newenv(xv._1)) = xv._2 )

            eval(Config(t, newenv))
          }
        case Fun(f, xs, t) => {
            FunClo( xs.foldLeft( env.env )( (a,b) => a+(b -> alloc(UnitV())) ), Fun(f, xs, t) )
          }
      }
 
      evalTo(config.t)
    }
  }

} 
 
