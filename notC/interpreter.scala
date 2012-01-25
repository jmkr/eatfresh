import java.io._
import scala.io._
import cs162.notC.syntax._
import scala.collection.mutable.{Map => MMap}

//---------- INTERPRETER ENTRY POINT ----------

object notC {
  import cs162.notC.interpreter._
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

package cs162.notC.interpreter {

//---------- SEMANTIC DOMAINS ----------

// abstract machine configuration. note that the configuration does
// not include a Store or a FunMap as specified by the formal
// semantics; as explained below this is because we take advantage of
// Scala's impure nature in order to have a global FunMap and a
// global, mutable store instead of threading it through the
// computation
case class Config(t:Term, env:Env)

// function map: Var -> FunctionDef
case class FunMap(funm:Map[Var, FunctionDef] = Map()) {
  def apply(x:Var): FunctionDef = funm get x match {
    case Some(fd) => fd
    case None => throw undefined("non-existent function")
  }
  def +(tup:Tuple2[Var, FunctionDef]): FunMap = FunMap(funm + tup)
}

// environment: Var -> Address
case class Env(env:Map[Var, Address] = Map()) {
  def apply(x:Var): Address = env get x match {
    case Some(a) => a
    case None => throw undefined("free variable")
  }
  def +(tup:Tuple2[Var, Address]): Env = Env(env + tup)
}

// store: Address -> Value
//
// we're taking advantage of Scala's impure nature to have a global,
// mutable store instead of threading it through the computation,
// which is why we use a mutable MMap instead of an immutable Map
case class Store(store:MMap[Address, Value] = MMap()) {
  def apply(a:Address): Value = store get a match {
    case Some(v) => v
    case None => throw undefined("non-existent address")
  }
}

// store addresses
case class Address(a:Int)

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
case class UnitV() extends Value { 
  override def toString = "unit" 
}

// companion objects for some of the above classes to provide implicit
// conversions (and a factory method for Address that provides unique
// addresses)
object FunMap { 
  implicit def funm2map(f:FunMap): Map[Var, FunctionDef] = f.funm
  implicit def map2funm(m:Map[Var, FunctionDef]): FunMap = FunMap(m)
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

// exception to be thrown when a program exhibits undefined behavior
case class undefined(msg:String) extends Exception(msg)

//---------- SEMANTIC HELPER FUNCTIONS ----------

// Note that neither inject nor alloc take or produce a Store as
// specified in the formal semantics. As described below, this is
// because we take advantage of Scala's impure nature in order to have
// a global, mutable store instead of threading it through the
// computation.

object SemanticHelpers {
  import Interp._

  // lift program to initial configuration. this is where we
  // initialize the global FunMap instead of actually putting it into
  // the initial configuration as specified by the formal semantics
  def inject(prog:Program): Config = { 

    // setup globalFunMap
    prog.fds.foldLeft()( (a,b) => globalFunMap + (b.f, b) )
    // return and empty environment 
    return Config(prog.t,Env())
  }

  // allocate value into store; unlike the helper function specified
  // in the semantics this one takes a single value and returns a
  // single address; in the implementation below (as opposed to the
  // semantic rules) it's easier to use this way
  def alloc(v:Value): Address = {
    val a = Address()
    gStore(a) = v
    return a
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
//
// similarly, the semantics threads a FunMap through the computation
// but no rule ever actually changes the FunMap. since the semantics
// behaves as if there was a single, global FunMap, our interpreter
// can implement the semantics using a global FunMap.

object Interp {
  import SemanticHelpers._

  // the global FunMap (initialized by the inject() helper function)
  var globalFunMap = FunMap()

  // the global Store
  val gStore = Store()

  // the evaluation function [[.]] \in Config -> Value
  def eval(config:Config): Value = {
    def evalTo(t:Term): Value = t match {
        case Seq(t1, t2) => {
            evalTo(t1)
            evalTo(t2)
        }
        case Assign(x, e) => gStore get config.env(x) match {
            case Some(_) => { gStore(config.env(x)) = evalTo(e); UnitV() }
            case _ => throw undefined("assigning to nonexistent variable")
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
            println(evalTo(e))
            UnitV()
        }
        case Num(n) => NumV(n)
        case Bool(b) => BoolV(b)
        case Str(str) => StringV(str)
        case NotUnit() => UnitV()
        case x:Var => gStore(config.env(x))
        case Not(e) => evalTo(e) match {
            case BoolV(b) => BoolV(!b)
            case _ => throw undefined("negated expression not a bool")
        }
        case BinOp(bop, e1, e2) => bop match {
            case Equal => {
              val v1 = evalTo(e1)
              val v2 = evalTo(e2)
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
            case NumT => NumV(BigInt(scala.Console.readInt()))
            case StrT => StringV(scala.Console.readLine())
        }
        case Call(f, es) => globalFunMap get f match {
          /*
          case Some(_) => { 
          }
          */
          case _ => throw undefined("assigning to nonexistent variable")
        }
        case Block(vbs, t) => {
            val xvs = for ( VarBind(x, e) <- vbs ) { 
              var addr = alloc(evalTo(e))
              // test lines
              println(x)
              println(addr)
              println(gStore(addr))
              // this line isn't working for some reason
              config.env.+(x, addr)
              //println(config.env(x))
            }
            evalTo(t)
        }
    }
    evalTo(config.t)
  }  
}

} // end package cs162.notC.interpreter
