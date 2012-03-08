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
    // FILL ME IN (slide 35/42 in 07-notML-implicit.pdf shows how)
    
    (type1, type2) match {
      case (_, _) if type1 == type2 => return
    	case (v @ TVar(_, Some(a)), _) => {
    		if( ! varsIn(type2).contains(v) ) v.parent = Some(type2)
    		else throw illTyped("tried to unify incompatible types")
    	}
    	case (_, v @ TVar(_, Some(a))) => {
    		if( ! varsIn(type1).contains(v) ) v.parent = Some(type1)
    		else throw illTyped("tried to unify incompatible types")
    	}
    	case (v @ TVar(_, _), ( NumT() | StrT() | TVar(_, Some(AL)) )) => {
    		v.parent = Some(type2)
    	}
    	case (( NumT() | StrT() | TVar(_, Some(AL)) ), v @ TVar(_, _)) => {
    		v.parent = Some(type1)
    	}
    	case (ListT(t1), ListT(t2)) => {
    		union(t1, t2)
    	}
    	case (FunT(ts1, t1), FunT(ts2, t2)) => {
    		if(ts1.length != ts2.length) throw illTyped("tried to unify incompatible types")
    		val args = ts1 zip ts2
    		args.map((ts) => union(ts._1, ts._2))
    		union(t1, t2)
    	}
    	case _ => throw illTyped("tried to unify incompatible types")
    }
  }

  // return a type's set representative; this function should use path
  // compression to optimize performance
  def find(typ:Type): Type = {
    // FILL ME IN
    typ match {
      case t @ TVar(x, a) => {
        if(t.parent == t) {
          return t
        } else {
          t.parent match {
            case Some(atype) => {
              val found = find(atype)
              t.parent = Some(found)
              return found
            }
            case _ => return typ
          }
        }
      }
      case _ => return typ
    }
  }

  // return all the type variables in a type
  def varsIn(typ:Type): Set[TVar] = {
    // FILL ME IN
    Set(TVar())
    typ match {
      case NumT() | BoolT() | StrT() | UnitT() => Set()
      case t @ TVar(x, a) => Set(t)
      case ListT(ltyp) => varsIn(ltyp)
      case FunT(ts, t) => {
        val theCoolestListEver = ts.foldLeft(Set[TVar]())( (a, b) => a.union(varsIn(b)) )
        theCoolestListEver.union(varsIn(t))
      }
    }
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
        union(env(x), evalTo(e))
        UnitT()
      }
      case w @ While(e, t) => {
        union(evalTo(e), BoolT())
        evalTo(t)
        UnitT()
      }
      case Out(e) => {
        evalTo(e)
        UnitT()
      }
      case HAssign(e1, e2) => {
        val t1 = evalTo(e1)
        val t2 = evalTo(e2)
        union(t1,ListT(TVar()))
        union(t2, TVar())
        UnitT()
      }
      case TAssign(e1, e2) => {
        val t1 = evalTo(e1)
        val t2 = evalTo(e2)
        union(t1,ListT(TVar()))
        union(t2, ListT(TVar()))
        UnitT()
      }
      case Num(n) => NumT()
      case Bool(b) => BoolT()
      case Str(str) => StrT()
      case NotUnit() => UnitT()
      case x:Var => env(x)
      case Not(e) => {
        union(evalTo(e), BoolT())
        BoolT()
      }
      case BinOp(bop, e1, e2) => bop match {
        case Equal => BoolT()
        case Or | And => {
          union(evalTo(e1), BoolT())
          union(evalTo(e2), BoolT())
          BoolT()
        }
        case Div | Mul | Sub => {
          union(evalTo(e1), NumT())
          union(evalTo(e2), NumT())
          NumT()
        }
        case Add => {
          union(evalTo(e1), TVar())
          union(evalTo(e2), TVar())
          evalTo(e1)
        }
        case Lte => {
          union(evalTo(e1), TVar())
          union(evalTo(e2), TVar())
          BoolT()
        }
        case Cons => {
          union(evalTo(e2), ListT(evalTo(e1)))
          evalTo(e2)
        }
        case _ => throw illTyped("tried to unify incompatible types")
      }
      case If(e, t1, t2) => {
        union(evalTo(e), BoolT())
        union(evalTo(t1), evalTo(t2))
        evalTo(t1)
      }
      case In(typ) => typ match {
        case NumT() => NumT()
        case BoolT() => BoolT()
        case _ => throw illTyped("input not num or string")
      }
      case Call(ef, es) => {
        // FILL ME IN
        //val fun = evalTo(ef)
        //union(evalTo(ef), fun)
        //es.map( (m) => union(TVar(), evalTo(m)) )
        TVar()
      }
      case NotList(es) => {
        // FILL ME IN
        evalTo(es.head)
      }
      case Head(e) => {
        union(evalTo(e), ListT(TVar()))
        evalTo(e)
      }
      case Tail(e) => {
        union(evalTo(e), ListT(TVar()))
        evalTo(e)
      }
      case Block(vbs, t) => {
        val dummies = for ( VarBind(x,_) <- vbs ) yield (x, TVar())
        val newEnv  = dummies.foldLeft( env )( (env, xv) => env + (xv._1 -> xv._2) )

        val dummies2= for ( VarBind(x,e) <- vbs ) yield (x, e)
        val typeList = dummies2.foldLeft(List[Type]())( (l, xv)  => l ::: List(evalTo(xv._2)) )
        
        val zippedList = dummies zip typeList
        zippedList.map( (m) => union(m._1._2, m._2) )

        //typeList.map( (m) => union(TVar(), m) )
		//println(newEnv)
        //val newEnv2 = dummies2.foldLeft( env )( (env, xv) => env + (xv._1 -> eval(Config(xv._2, newEnv))))
		//println(newEnv2)
        eval(Config(t, newEnv))
      }
      case Fun(f, xs, t) => {
        if( evalTo(f) == evalTo(t) ) return evalTo(f)
        else throw illTyped("function type and return type mismatch")
      }
    }

    evalTo(config.t)
  }
}

}
