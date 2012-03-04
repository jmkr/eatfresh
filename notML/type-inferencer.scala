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
    
    // v This doesnt work lol v
    /*typ match {
      case t @ TVar(x, a) => {
        if(t.parent == t) {
          return t
        } else {
          t.parent match {
            case t2 @ Some(Type) => {
              t2 = find(t2)
              return t2
            }
            case _ => return t
          }
        }
      }
    }*/
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
      case Seq(t1, t2) => {
        evalTo(t1)
        return evalTo(t2)
      }
      case Assign(x, e) => {
        if(evalTo(e) == env(x)) UnitT()
        else throw illTyped("Assignment type miss-match!!!!!!")
      }
      case w @ While(e, t) => evalTo(e) match {
        case BoolT() => {
          evalTo(t)
          UnitT()
        }
        case _ => throw illTyped("While expression mishap!")
      }
      case Out(e) => evalTo(e) match {
        case BoolT() => UnitT()
        case NumT() => UnitT()
        case StrT() => UnitT()
        case FunT(ts, t) => UnitT()
        case ListT(t) => UnitT()
        case _ => throw illTyped("Output expression mishap!")
      }
      case HAssign(e1, e2) => {
        // FILL ME IN
        e1 match {
          case _ => UnitT()
        }
      }
      case TAssign(e1, e2) => {
        // FILL ME IN
        e1 match {
          case _ => UnitT()
        }
      }
      case Num(n) => NumT()
      case Bool(b) => BoolT()
      case Str(str) => StrT()
      case NotUnit() => UnitT()
      case x:Var => env(x)
      case Not(e) => evalTo(e) match {
        case _ => BoolT()
      }
      case BinOp(bop, e1, e2) => bop match {
        case Equal => BoolT()
        case _ => (evalTo(e1), evalTo(e2)) match {
          case (BoolT(), BoolT()) => bop match {
            case And => BoolT()
            case Or  => BoolT()
            case _   => throw illTyped("illegal operation on bools")
          }
          case (NumT(), NumT()) => bop match {
            case Add => NumT()
            case Sub => NumT()
            case Mul => NumT()
            case Div => NumT()
            case Lte => BoolT()
            case _   => throw illTyped("illegal operation on nums")
          }
          case (StrT(), StrT()) => bop match {
            case Add => StrT()
            case Lte => BoolT()
            case _   => throw illTyped("illegal operation on strings")
          }
          case (_, ListT(typ)) => bop match {
            case Cons => ListT(typ)
            case _ => throw illTyped("illegal operation on lists")
          }
          case _ => throw illTyped("illegal binary operation")
        }
      }
      case If(e, t1, t2) => evalTo(e) match {
        // FILL ME IN
        case _ => UnitT()
      }
      case In(typ) => typ match {
        // FILL ME IN
        case _ => UnitT()
      }
      case Call(ef, es) => {
        // FILL ME IN
        UnitT()
      }
      case NotList(es) => {
        // FILL ME IN
        UnitT()
      }
      case Head(e) => evalTo(e) match {
        // FILL ME IN
        case _ => UnitT()
      }
      case Tail(e) => evalTo(e) match {
        // FILL ME IN
        case _ => UnitT()
      }
      case Block(vbs, t) => {
        val dummies = for ( VarBind(x,_) <- vbs ) yield (x, UnitT())
        val newEnv  = dummies.foldLeft( env )( (env, xv) => env + (xv._1 -> xv._2) )
        val dummies2= for ( VarBind(x,e) <- vbs ) yield (x, e)
        val newEnv2 = dummies2.foldLeft( env )( (env, xv) => env + (xv._1 -> eval(Config(xv._2, newEnv))))
        eval(Config(t, newEnv2))
      }
      case Fun(f, xs, t) => {
        // FILL ME IN
        UnitT()
      }
    }

    evalTo(config.t)
  }
}

}
