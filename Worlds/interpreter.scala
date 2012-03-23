// John Meeker
// Ken Hwang

import java.io._
import scala.io._
import cs162.Worlds.syntax._
import scala.collection.mutable.{Map => MMap}

//---------- INTERPRETER ENTRY POINT ----------

object Worlds {
  import cs162.Worlds.interpreter._
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

package cs162.Worlds.interpreter {
	
	//---------- SEMANTIC DOMAINS ----------
	
	// abstract machine configuration. note that the configuration does
	// not include a Store as specified by the formal semantics; as
	// explained below this is because we take advantage of Scala's impure
	// nature in order to have a global, mutable store instead of
	// threading it through the computation
	//case class Config(t:Term, world:World)
	case class Config(t:Term, env:Env)

	// environment: Var -> Address
	case class Env(env:Map[Var, Address] = Map()) extends Value {
	  def apply(x:Var): Address = {
	    env get x match {
	      case Some(a) => a
	      case None => {
                  print(x)
                  throw undefined("free variable")
              }
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
	
	//not needed, apparently
	case class World(env:Map[Var, Address] = Map(), p:Value = UnitV()) extends Value {
	  def apply(x:Var): Address = {
	    env get x match {
	      case Some(a) => a
	      case None => throw undefined("free variable")
	    }
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
                def inject(prog:Program): Config = { 
                var env = Env()
                val parent = alloc(env)
                env = env+(Var("parent") -> parent)
                env = env+(Var("self") -> parent)
                Config(prog.t, env) 
                }

                //def inject(prog:Program): Config = { Config(prog.t, World(Env(), UnitV())) }
	
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
		def lookProto(o:Object, str:String): Value = o.o get str match {
		    case Some(v) => v
		    case None => o.o get "proto" match {
		      case None => UnitV()
		      case Some(a:Address) => gStore(a) match {
				case o:Object => lookProto(o, str)
				case _ => throw undefined("proto doesn't refer to an object")
		      }
		      case _ => throw undefined("proto isn't an address")
		    }
		}
		
		
		// TODO:: look up variable in world
		///////----------------------------
		/////////////----------------------
		
		
		//TODO:: create a new world aka sprout
		def newWorld(pw:World): World = {
		  	val newEnv = pw.env.foldLeft( Env() )( (env, xv) => { 
			    //println(xv._1 + " -> " + gStore(xv._2.asInstanceOf[Address]))
			    env + (xv._1 -> alloc(gStore(xv._2.asInstanceOf[Address]))) 
			  } )
		    val newWorld = World(newEnv, pw)
		    gStore(newWorld.env(Var("thisWorld"))) = newWorld
		    newWorld
	  	}
	
	}	
		
		//TODO:: make update process to push changes from parent world to child environment 
		
		//TODO:: make compare method to compare changes between two worlds 
		
		
	
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
					//TODO:: world assignment?
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
				// NOTE: if we try to output an object whose fields
				// recursively refer back to that object, then this code will
				// go into an infinite loop					
					def val2str(v:Value): String = v match {
		  				case a:Address => "[" + obj2str(a) + "]"
		  				case StringV(s) if s == "" => "\"\""
						
						//TODO:: world out
						//case w @ World(e, p) => "[" + w + "]"
		  				
						case other => other.toString
					}
					
					//TODO::mod obj2str for worlds
					def obj2str(a:Address): String = gStore(a) match {												
						//ORIG
		  				case Object(o) => o.foldLeft( "" ){ 
		    				case (s, (str, v)) => s + ", " + str + " : " + val2str(v) 
		  				}		  				
						case _ => throw undefined("outputting illegal value")			
					}					
					println(val2str(evalTo(e)))
					UnitV()
	      		}
	
				//TODO:: mod update for worlds
	      		case Update(e1, e2, e3) => (evalTo(e1), evalTo(e2), evalTo(e3)) match {
					case (a:Address, StringV(str), v:Value) => gStore(a) match {
		  				case o:Object => {
		    				gStore(a) = o + (str -> v)
		    				UnitV()
		  				}
		  				case _ => throw undefined("update: address of non-object")
					}
					case _ => throw undefined("illegal object update")
	      		}
	
	      		case Num(n) => NumV(n)
	      		case Bool(b) => BoolV(b)
	      		case Str(str) => StringV(str)
	      		case NotUnit() => UnitV()
	      		case x:Var => gStore(env(x))
	      		case Not(e) => evalTo(e) match {
					case BoolV(b) => BoolV( !b )
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
		  				BoolV( v1 == v2 )
					}
					case _ => (evalTo(e1), evalTo(e2)) match {
		  				case (BoolV(b1), BoolV(b2)) => bop match {
		    				case And => BoolV( b1 && b2 )
		    				case Or  => BoolV( b1 || b2 )
		    				case _   => throw undefined("illegal operation on bools")
		  				}
		  				case (NumV(n1), NumV(n2)) => bop match {
		    				case Add => NumV( n1 + n2 )
	            			case Sub => NumV( n1 - n2 )
		    				case Mul => NumV( n1 * n2 )
		    				case Div if n2 != 0 => NumV( n1 / n2 )
		    				case Lte => BoolV( n1 <= n2 )
		    				case _   => throw undefined("illegal operation on nums")
		  				}
		  				case (StringV(s1), StringV(s2)) => bop match {
		    				case Add => StringV( s1 + s2 )
		    				case Lte => BoolV( s1 <= s2 )
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
					case NumT => NumV( BigInt(scala.Console.readLine()) )
					case StrT => StringV( scala.Console.readLine() )
	      		}
	      		case Call(ef, es) => evalTo(ef) match {
					case clo @ FunClo(cloEnv, Fun(f, xs, t)) => {
		  				if (xs.length != es.length) 
		    				throw undefined("arguments and parameters don't match")
		  
		  				val xv = (f :: xs) zip (clo :: (es map evalTo))
		  				val newEnv = xv.foldLeft( cloEnv )((env, xv) => env + (xv._1 -> alloc(xv._2)) )
		  				//eval(Config(t, newEnv))
						eval(Config(t, newEnv))		
					}
					case _ => throw undefined("calling a non-closure")
	      		}
	      		case Block(vbs, t) => {
					//TODO::add current world to block
					
					val dummies = for ( VarBind(x,_) <- vbs ) yield (x, UnitV())
					val newEnv = dummies.foldLeft( env )((env, xv) => env + (xv._1 -> alloc(xv._2)) )
		
					for ( VarBind(x, e) <- vbs ) gStore(newEnv(x)) = eval(Config(e, newEnv))
					
					eval(Config(t, newEnv))
	      		}
	      		case f:Fun => FunClo(env, f)
	
	      		case Obj(fbs) => {
					val o = fbs.foldLeft( Object() )(
		  			(o,fb) => o + (fb.s.str -> evalTo(fb.e)) )
					alloc(o)
	      		}
			
				//TODO:: add commit and sprout operations to access
	      		case Access(e1, e2) => (evalTo(e1), e2) match {
					case (a:Address, s:Str) => gStore(a) match { 
						case o @ Object(m) => lookProto(o, s.str)
						case _ => throw undefined("access: address of a non-object")
					}
					case (w:Env, c:Call) => c.ef match {
						case Var(x) => x match {							
							//TODO:: sprout
							case "sprout" => {
								var newenv = Env(w)
                                                                gStore(newenv(Var("parent"))) = env(Var("self"))
                                                                val self = alloc(newenv)
                                                                newenv = newenv+(Var("self") -> self)
                                                                self
							}
                                                        case "commit" => {
                                                            w(Var("self"))
                                                        }							
                                                        case _ => throw undefined("illegal object field access2")
                                                }
                                                
                                                case _ => throw undefined("illegal object field access3")
                                        }
                                        
                                        case (a:Address, v:Var) => (gStore(a), v.x) match{
                                            case (w:Env, "commit") => {
                                                println("committing!")
                                                UnitV()
                                            }
                                            case _ => { throw undefined("oh nose!") }
                                        }
                                            
//                                            case Var("sprout") => {
//                                                w match {
//                                                  case w:Env => {
//                                                      var newenv = Env(w)
//                                                                gStore(newenv(Var("parent"))) = env(Var("self"))
//                                                                val self = alloc(newenv)
//                                                                newenv = newenv+(Var("self") -> self)
//                                                          self
//                                                  }
//                                                }
//								
//							}
//                                              case Var("commit") => {
//                                                            println("caught!!")
//                                                            UnitV()
//                                                  }	
//                                        }
                                       
                                  case _ => {
                                      println(e1)
                                      println(e2)
                                      throw undefined("illegal object field access4")
                                  }
                        } 
				//ORIG
				/*case Access(e1, e2) => (evalTo(e1), evalTo(e2)) match {
					case (a:Address, StringV(str)) => gStore(a) match {
		  				case o:Object => lookProto(o, str)
		  				case _ => throw undefined("access: address of a non-object")
					}
					case _ => throw undefined("illegal object field access")
	      		}*/
				
				//TODO:: this is how sprouting should be handled
                        case Sprout() => {
                                //val newWorld = World(Env(), UnitV());
                                //gStore(Address()) = newWorld					
//                                var newenv = Env(env)
//                                newenv = newenv+(Var("parent") -> Address())
//                                gStore(newenv(Var("parent"))) = env
                                
                                val newenv = env.foldLeft(Env())(
                                  (e, xv) => { 
                                    if (xv._1==Var("parent") ){ 
                                      e+ (xv._1 -> env( Var("self") ) )
                                    }else{
                                      e+ (xv._1 -> alloc(gStore(xv._2)))
                                    }
                                  } )
                                

            
                                val self = alloc(newenv)  
                                val newerenv = newenv+( Var("self") -> self) 
                                self
                                //eval(Config(t, newenv))			
                        }
	
				//TODO:: add inside block functionality
			case Inside(w, t) => evalTo(w) match {
				case world:Address => {
                                    gStore(world) match {
                                      case e:Env => {
                                          //println("inside")
   //                                       println(gStore)
    //                                      println(world)
     //                                     println()
     //                                     println
//println(e(Var("self")))
                        eval(Config(t, e))
                                      }
                                      case _ => {}
                                    }
                                    BoolV(true)
                                }
				case eeh @ _ => {
                                    print(eeh)
                                    throw undefined("illegal within on non-world")
                                }
			}
                        case Commit(w) => { w match {
                                                 
                        
                        case a:Address => {
                            gStore(a) match {

                            case ee:Env => {
                                
                            gStore(ee(Var("parent"))) match {
                              case eee:Env => {
                                  eval(Config(t,eee))
                                  UnitV()
                              }
                              case _ => {UnitV()}
                            }

                            }
                            case _ => {UnitV()}      
                  }
                          }
                             
              
                        }
      
            
                        }
		
	      		case m:Method => MethClo(env, m)
	
	      		case MCall(er, ef, es) => (evalTo(er), evalTo(ef)) match {
					case (a:Address, StringV(str)) => gStore(a) match {
		  				case o:Object => lookProto(o, str) match {
		    				case MethClo(cloEnv, Method(xs, t)) => {
		      					if (xs.length != es.length) 
									throw undefined("arguments and parameters don't match")
	
		      					val self = Var("self")
		      					val xvs = (self :: xs) zip (a :: (es map evalTo))
		      					val newEnv = xvs.foldLeft( cloEnv )((env, xv) => env + (xv._1 -> alloc(xv._2)) )
		      					eval(Config(t, newEnv))
		    				}
		    				case _ => throw undefined("calling a non-method")
		  				}
		  				case _ => throw undefined("method call on non-object")
					}
					case _ => throw undefined("illegal method call")
	      		}
		
				/*
				case VarBind(x, e) => {
					gStore(env(x)) match {
						case w @ World(e,p) => {
							//TODO::
							
							
						}
						case _ => UnitV()						
					}
					UnitV()
				}*/
	    	}
	    	evalTo(config.t)
		}
	}

} // end package cs162.Worlds.interpreter
