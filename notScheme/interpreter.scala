import java.io._
import scala.io._
import cs162.notScheme.syntax._
import scala.collection.mutable.{Map => MMap}

//---------- INTERPRETER ENTRY POINT ----------

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

// exception to be thrown when a program exhibits undefined behavior
case class undefined(msg:String) extends Exception(msg)

//---------- SEMANTIC HELPER FUNCTIONS ----------

// Note that none of inject, alloc, or makeList take or produce a
// Store as specified in the formal semantics. As described below,
// this is because we take advantage of Scala's impure nature in order
// to have a global, mutable store instead of threading it through the
// computation.

object SemanticHelpers {
  import Interp._

  // lift program to initial configuration.
  def inject(prog:Program): Config = {
    return Config(prog.t,Env())
  }

  // allocate value into store; unlike the helper function specified
  // in the semantics this one takes a single value and returns a
  // single address; in the implementation below (as opposed to the
  // semantic rules) it's easier to use this way
  def alloc(v:Value): Address = {
    val a = Address()
    gStore(a) = v
    a
  }

  // convert a list of values into a ListV of values (returning the
  // address from store-allocating the ListV)
  def makeList(vs:List[Value]): Address = {
    def makeCell(v:Value, a:Address): Address = alloc( ListF(v, alloc(v)) )
    vs.foldRight( alloc(Empty()) ) (makeCell)
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
      case Out(e) => // FILL ME IN
      case HAssign(e1, e2) => // FILL ME IN
      case TAssign(e1, e2) => // FILL ME IN
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
	  // FILL ME IN
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
	  case (v:Value, a:Address) => // FILL ME IN
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
      case Call(ef, es) => // FILL ME IN
      case NotList(es) => // FILL ME IN
      case Head(e) => // FILL ME IN
      case Tail(e) => // FILL ME IN
      case Block(vbs, t) => // FILL ME IN
    }

    evalTo(config.t)
  }
}

} // end package cs162.notScheme.interpreter
