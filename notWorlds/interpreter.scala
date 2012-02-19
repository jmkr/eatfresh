// James Ebentier
// David Schnurr
// Vincent Alindogan


import java.io._
import scala.io._
import cs162.notWorlds.syntax._
import scala.collection.mutable.{Map => MMap}

//---------- INTERPRETER ENTRY POINT ----------

object notWorlds {
  import cs162.notWorlds.interpreter._
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

package cs162.notWorlds.interpreter {

//---------- SEMANTIC DOMAINS ----------

// abstract machine configuration. note that the configuration does
// not include a Store as specified by the formal semantics; as
// explained below this is because we take advantage of Scala's impure
// nature in order to have a global, mutable store instead of
// threading it through the computation
case class Config(t:Term, env:Env)

// environment: Var -> Address
case class Env(env:Map[Var, Address] = Map()) {
  def apply(x:Var): Address = {
    env get x match {
      case Some(a) => a
      case None => throw undefined("free variable")
    }
  }
  def +(tup:Tuple2[Var, Address]): Env = Env(env + tup)
}

// store: Address -> Value
//
// we're taking advantage of Scala's impure nature to have a global,
// mutable store instead of threading it through the computation,
// which is why we use a mutable Map instead of an immutable Map
case class Store(store:MMap[Address, Value] = MMap()) {
  def apply(a:Address): Value = {
    store get a match {
      case Some(v) => v
      case None => throw undefined("non-existent address")
    }
  }
}

// language values
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
case class Address(a:Int) extends Value
case class Object(o:Map[String, Value] = Map()) extends Value {
  def apply(str:String): Value = {
    o get str match {
      case Some(v) => v
      case None => UnitV()
    }
  }
  def +(tup:Tuple2[String, Value]): Object = Object(o + tup)
  override def toString = o.toString
}
case class World(env:Map[Var, Address] = Map(), p:Value = UnitV()) extends Value {
  def apply(x:Var): Address = {
    env get x match {
      case Some(a) => a
      case None => throw undefined("free variable")
    }
  }
  def sprout(pw): World = {
	World(env, w)
  }
}
sealed abstract class Closure extends Value {
  override def toString = "<closure>" 
}
case class FunClo(env:Env, fun:Fun) extends Closure
case class MethClo(env:Env, m:Method) extends Closure
case class UnitV() extends Value { 
  override def toString = "unit" 
}

// companion objects for some of the above classes to provide implicit
// conversions (and a factory method for Address that provides unique
// addresses)
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
object Object {
  implicit def obj2map(o:Object): Map[String, Value] = o.o
  implicit def map2obj(m:Map[String, Value]): Object = Object(m)
}

// exception to be thrown when a program exhibits undefined behavior
case class undefined(msg:String) extends Exception(msg)

//---------- SEMANTIC HELPER FUNCTIONS ----------

// Note that none of inject, alloc, or lookProto take or produce a
// Store as specified in the formal semantics. As described below,
// this is because we take advantage of Scala's impure nature in order
// to have a global, mutable store instead of threading it through the
// computation.

object SemanticHelpers {
  import Interp._

  // lift program to initial configuration.
  def inject(prog:Program): Config = { Config(prog.t, Env()) }

  // allocate value into store; unlike the helper function specified
  // in the semantics this one takes a single value and returns a
  // single address; in the implementation below (as opposed to the
  // semantic rules) it's easier to use this way
  def alloc(v:Value): Address = {
    val a = Address()
    gStore(a) = v
    a
  }

  // look up a field in the prototype chain of a record
  def lookProto(o:Object, str:String): Value = {
    o(str) match {  // if str exists in o return o(str)
      case Address(a) => gStore(Address(a))
      case _ => {
        o("proto") match { // else find "proto" and recurse through object
          case Address(a) => {
            gStore(Address(a)) match {
              case Object(m) => lookProto(Object(m), str)
              case Address(a2) => gStore(Address(a2)) match {
              	case Object(m) => lookProto(Object(m), str) 
              	case _ => throw undefined("proto isn't an address")
              }
              case _ => throw undefined("proto isn't an address")
            }
          } 
          case _ => throw undefined("proto isn't an address")
        }
      }
    }
  }
    
}

//---------- INTERPRETER ----------

// the formal semantics is necessarily completely pure, meaning there
// is no mutable state. this implies that we need to thread the store
// through the computation as part of the abstract machine
// configuration, taking in one store and passing on a (potentially
// different) new store. The intent of the semantics is that the store
// behaves identically to having a single global, mutable store.
//
// our interpreter has to behave exactly the same as the formal
// semantics, but it doesn't have to be implemented exactly the same
// way (as long as it's guaranteed that the behavior is the
// same). since Scala supports mutable state, and since the semantics
// *acts* as if there's a single global, mutable store, our
// interpreter can simply use a global, mutable store instead of
// making it part of the machine configuration and threading it
// through the computation.

object Interp {
  import SemanticHelpers._

  // the global Store
  val gStore = Store()

// the evaluation function [[.]] \in Config -> Value
def eval(config:Config): Value = {
	val env = config.env

	// since we'll be making lots of recursive calls where the
	// environment doesn't change, we'll define an inner function that
	// will leave env as a free variable
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
		case Out(e) => {
			def val2str(v:Value): String = v match {
				case a:Address => "[" + obj2str(a) + "]"
				case StringV(s) if s == "" => "\"\""
				case other => other.toString
			}
			def obj2str(a:Address): String = gStore(a) match {
				case Object(m) => {
					if(m.size==0) ""
					else {
						m.foldLeft("") ( (s, b) => b._2 match { case Address(a2) => s + ", " + b._1 + " : " + val2str(gStore(Address(a2))); case _ => s } )
					}
				}
				case _ => throw undefined("error in Out")
			}
			println(val2str(evalTo(e)))
			UnitV()
		}
		case Update(e1, e2, e3) => (evalTo(e1), evalTo(e2), evalTo(e3)) match {
			case (a:Address, s:StringV, v:Value) => gStore(a) match { 
				case o @ Object(m) => {
					o(s.str) match {
						case adr @ Address(a2) => { 
							gStore(adr) = v
							UnitV()
						}
						case _ => {
							gStore(a) = o + (s.str -> alloc(v))
							UnitV()
						}
					}
				}
				case _ => throw undefined("illegal object update")
			}
			case _ => throw undefined("illegal object update")
			UnitV()
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
				val v1 = evalTo(e1) match {
					case a:Address => gStore(a)
					case v => v
				}
				val v2 = evalTo(e2) match {
					case a:Address => gStore(a)
					case v => v
				}
				BoolV(v1 == v2)
			}
			case _ => (evalTo(e1), evalTo(e2)) match {
				case (BoolV(b1), BoolV(b2)) => bop match {
					case And => BoolV(b1 && b2)
					case Or  => BoolV(b1 || b2)
					case _   => throw undefined("illegal operation on bools")
				}
				case (NumV(n1), NumV(n2)) => bop match {
					case Add => NumV(n1 + n2)
					case Sub => NumV(n1 - n2)
					case Mul => NumV(n1 * n2)
					case Div if n2 != 0 => NumV(n1 / n2)
					case Lte => BoolV(n1 <= n2)
					case _   => throw undefined("illegal operation on nums")
				}
				case (StringV(s1), StringV(s2)) => bop match {
					case Add => StringV(s1 + s2)
					case Lte => BoolV(s1 <= s2)
					case _   => throw undefined("illegal operation on strings")
				}
				case _ => throw undefined("illegal binary operation")
			}
		}
		case If(e, t1, t2) => evalTo(e) match {
			case BoolV(true)  => evalTo(t1)
			case BoolV(false) => evalTo(t2)
			case _ => throw undefined("if guard not a bool")
		}
		case In(typ) => typ match {
			case NumT => NumV(BigInt(scala.Console.readLine()))
			case StrT => StringV(scala.Console.readLine())
		}
		case Obj(fbs) => {
			alloc( fbs.foldLeft(Object(Map[String, Value]()))( (a, b) => a + (b.s.str -> alloc(evalTo(b.e))) ) )
		}
		case Access(e1, e2) => (evalTo(e1), e2) match {
			case (a:Address, s:Str) => gStore(a) match { 
				case o @ Object(m) => lookProto(o, s.str)
				case _ => throw undefined("illegal object field access")
			}
			case (w @ World(e, p), c:Call) => c.ef match {
				case Var(x) => x match {
					case "sprout" => {
						// FILL ME IN
						w.sprout()
						UnitV()
					}
					case "commit" => {
						println("foundcommit")
						UnitV()
					}
					case "update" => {
						println("foundupdate")
						UnitV()
					}
					case _ => throw undefined("illegal object field access")
				}
				case _ => throw undefined("illegal object field access")
			}
			case _ => throw undefined("illegal object field access")
		}
		case Within(w, t) => UnitV()
		case MCall(eO, eF, es) => (evalTo(eO), evalTo(eF)) match {
			case (a:Address, s:StringV) => gStore(a) match {
				case o @ Object(m) => lookProto(o, s.str) match {
					case clo @ MethClo(cloEnv, Method(xs, t)) => {
						if (xs.length != es.length) 
							throw undefined("arguments and parameters don't match")
            		
						val xv = (Var("self") :: xs) zip (a :: (es map evalTo))
						val newEnv = xv.foldLeft( cloEnv )(
							(env, xv) => env + (xv._1 -> alloc(xv._2)))
							eval(Config(t, newEnv))
					}
					case _ => {
						throw undefined("calling a non-method")
					}
				}
				case _ => throw undefined("calling a non-method")
			}
			case _ => throw undefined("calling a non-method")
		}
		case Call(ef, es) => evalTo(ef) match {
			case clo @ FunClo(cloEnv, Fun(f, xs, t)) => {
				if (xs.length != es.length) 
					throw undefined("arguments and parameters don't match")

				val xv = (f :: xs) zip (clo :: (es map evalTo))
				val newEnv = xv.foldLeft( cloEnv )(
					(env, xv) => env + (xv._1 -> alloc(xv._2)))
					eval(Config(t, newEnv))
			}
			case _ => throw undefined("calling a non-closure")
		}
		case Block(vbs, t) => {
			val worldVbs = List(VarBind(Var("thisWorld"), NotUnit())) ::: vbs  //add thisworld first
			val dummies = for ( VarBind(x,_) <- worldVbs ) yield (x, UnitV())
			val newEnv = dummies.foldLeft( env )((env, xv) => env + (xv._1 -> alloc(xv._2)) )
			for ( VarBind(x, e) <- worldVbs ) gStore(newEnv(x)) = eval(Config(e, newEnv))
			gStore(newEnv(Var("thisWorld"))) = World(Map[Var, Address]()) //set thisWorld using current environment
			eval(Config(t, newEnv))
		}
		case f:Fun => FunClo(env, f)
		case m:Method => MethClo(env, m)
	}

	evalTo(config.t)
	}
}

} // end package cs162.notWorlds.interpreter