import java.io._
import scala.io._
import cs162.notML.syntax._

//---------- TYPE INFERENCER ENTRY POINT ----------

object notML {
  import cs162.notML.typeInferencer._
  import SemanticHelpers._
  import Infer._

  def main(args:Array[String]) {
    val ast = ParseL.getAST(Source.fromFile(args(0)).mkString)

    if (args.length == 1 || args(1) != "--printast") 
      println(find(eval(inject(ast))))
    
    else PrettyPrint.writeDot(ast, "ast.dot")
  }
}

package cs162.notML.typeInferencer {

//---------- TYPE INFERENCER SEMANTIC DOMAINS ----------

// abstract machine configuration
case class Config(t:Term, env:Env)

// environment: Var -> Type
case class Env(env:Map[Var, Type] = Map()) {
  def apply(x:Var): Type = env get x match {
    case Some(typ) => typ
    case None => throw illTyped("free variable")
  }
  def +(tup:Tuple2[Var, Type]): Env = Env(env + tup)
}

// environment companion object
object Env { 
  implicit def env2map(e:Env): Map[Var, Type] = e.env
  implicit def map2env(m:Map[Var, Type]): Env = Env(m)
}

// exception to be thrown when a program is ill-typed
case class illTyped(msg:String) extends Exception(msg)

//---------- SEMANTIC HELPER FUNCTIONS ----------

object SemanticHelpers {
  // lift program to initial configuration
  def inject(prog:Program): Config = { Config(prog.t, Env()) }

  // union two types. unlike the semantics this actually performs the
  // type unification using the union-find data structure; hence it
  // returns Unit instead of Bool and throws an illTyped exception if
  // the unification fails
  //
  // NOTE: the find() function should use path compression, but this
  // union() function should NOT use union-by-rank; when unioning a
  // type variable T with something else, T always sets its parent to
  // that other type
  //
  def union(type1:Type, type2:Type): Unit = {
    // FILL ME IN
    UnitT()

  }

  // return a type's set representative; this function should use path
  // compression to optimize performance
  def find(typ:Type): Type = {
    // FILL ME IN
    UnitT()
  }

  // return all the type variables in a type
  def varsIn(typ:Type): Set[TVar] = {
    // FILL ME IN
    Set(TVar())
  }
}

//---------- TYPE INFERENCER ----------

object Infer {
  import SemanticHelpers._

  def eval(config:Config): Type = {
    val env = config.env

    // since we'll be making lots of recursive calls where the
    // environment doesn't change, we'll define an inner function that
    // will leave env as a free variable
    def evalTo(t:Term): Type = t match {
      case Seq(t1,t2) => {
        evalTo(t1)
      }
      case Assign(x,e) => {
        evalTo(e)
      }
      case While(e,t) => {
        evalTo(t)
      }
      case Out(e) => {
        evalTo(e)
      }
      case HAssign(e1,e2) => {
        evalTo(e2)
      }
      case TAssign(e1,e2) => {
        evalTo(e2)
      }
      case Num(n) => {
        NumT()
      }
      case Bool(b) => {
        BoolT()
      }
      case Str(str) => {
        StrT()
      }
      case NotUnit() => {
        BoolT()
      }
      case Var(x) => {
        UnitT()
      }
      case Not(e) => {
        BoolT()
      }
      case BinOp(op,e1,e2) => {
        evalTo(e2)
      }
      case If(e,t1,t2) => {
        evalTo(t2)
      }
      case In(tp) => {
        UnitT()
      }
      case Call(ef,es) => {
        evalTo(ef)
      }
      case NotList(es) => {
        UnitT()
      }
      case Head(e) => {
        evalTo(e)
      }
      case Tail(e) => {
        evalTo(e)
      }
      case Block(vds,t) => {
        UnitT()
      }
      case Fun(f,xs,t) => {
        UnitT()
      }
    }

    evalTo(config.t)
  }
}

}