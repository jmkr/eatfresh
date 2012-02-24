package cs162.worlds.syntax

import java.io._
import scala.io._

//---------- AST ----------

sealed abstract class AST
sealed abstract class Term extends AST

// programs
case class Program(fds:List[FunctionDef], t:Term) extends AST

// function definitions
case class FunctionDef(f:Var, xs:List[Var], t:Term) extends AST

// commands
sealed abstract class Cmd extends Term
case class Seq(t1:Term, t2:Term) extends Cmd
case class Assign(x:Var, e:Exp) extends Cmd
case class While(e:Exp, t:Term) extends Cmd
case class Out(e:Exp) extends Cmd
case class Sprout(w1:Var, w2:Var) extends Cmd
case class Commit(w:Var) extends Cmd

// expressions
sealed abstract class Exp extends Term
case class Num(n:BigInt) extends Exp
case class Bool(b:Boolean) extends Exp
case class Str(str:String) extends Exp
case class NotUnit() extends Exp
case class Var(x:String) extends Exp
case class Not(e:Exp) extends Exp
case class BinOp(op:Bop, e1:Exp, e2:Exp) extends Exp
case class If(e:Exp, t1:Term, t2:Term) extends Exp
case class In(typ:InputType) extends Exp
case class Call(f:Var, es:List[Exp]) extends Exp
case class Block(vds:List[VarBind], t:Term) extends Exp

// bindings for Block
case class VarBind(x:Var, e:Exp) extends AST

// types for input
sealed abstract class InputType
case object NumT extends InputType
case object StrT extends InputType

// binary operators
sealed abstract class Bop
case object Add extends Bop
case object Sub extends Bop
case object Mul extends Bop
case object Div extends Bop
case object Equal extends Bop
case object Lte extends Bop
case object And extends Bop
case object Or extends Bop

//---------- AST PRETTY-PRINTER ----------

object PrettyPrint { 
  // output AST graph to file in dot format
  def writeDot(ast: AST, file: String) {
    val out = new PrintWriter(new BufferedWriter(new FileWriter(file)))
    
    var nodeid = 0
    def getid() = { nodeid += 1; nodeid }
    
    def printNode(id:Int, lbl:String, box:Boolean = false) {
      out.print(id + " [")
      if (box) { out.print("shape=box, ") }
      out.println("label=\"" + lbl + "\"];")
    }
    
    def printEdges(id:Int, lbls:List[Int]) {
      lbls map ((lbl) => { out.println(id + " -> " + lbl) })
    }

    def output(node: AST): Int = node match {
      case Program(fds, t) => {
	val lbls = (fds map output) ::: List(output(t))
	val myLbl = getid
	
	printNode(myLbl, "Program", true)
	printEdges(myLbl, lbls)
	myLbl
      }
      case Seq(t1, t2) => {
	val c1Lbl = output(t1)
	val c2Lbl = output(t2)
	val myLbl = getid
	
	printNode(myLbl, ";")
	printEdges(myLbl, List(c1Lbl, c2Lbl))
	myLbl
      }
      case Assign(Var(x), rhs) => {
	val rhsLbl = output(rhs)
	val myLbl = getid
	
	printNode(myLbl, x + " :=")
	printEdges(myLbl, List(rhsLbl))
	myLbl
      }
      case While(e, t) => {
	val guardLbl = output(e)
	val bodyLbl = output(t)
	val myLbl = getid
	
	printNode(myLbl, "while")
	printEdges(myLbl, List(guardLbl, bodyLbl))
	myLbl
      }
      case Out(e) => {
	val eLbl = output(e)
	val myLbl = getid
	
	printNode(myLbl, "output")
	printEdges(myLbl, List(eLbl))
	myLbl
      }
      case Num(n) => {
	val myLbl = getid
	printNode(myLbl, n.toString)
	myLbl
      }
      case Bool(b) => {
	val myLbl = getid
	printNode(myLbl, b.toString)
	myLbl
      }
      case Str(str) => {
	val myLbl = getid
	printNode(myLbl, "\\\"" + str + "\\\"")
	myLbl	
      }
      case NotUnit() => {
	val myLbl = getid
	printNode(myLbl, "unit")
	myLbl
      }
      case Var(x) => {
	val myLbl = getid
	printNode(myLbl, x)
	myLbl
      }
	case Sprout(w1, w2) => {
	val myLbl = getid
	//printNode(myLbl, w2)
	myLbl
      }
	case Commit(w) => {
	val myLbl = getid
	//printNode(myLbl, w2)
	myLbl
      }
      case Not(e) => {
	val eLbl = output(e)
	val myLbl = getid
	
	printNode(myLbl, "!")
	printEdges(myLbl, List(eLbl))
	myLbl
      }
      case BinOp(op, e1, e2) => {
	val e1Lbl = output(e1)
	val e2Lbl = output(e2)
	val myLbl = getid
	
	val sym = op match {
	  case Add => "+"
	  case Sub => "-"
	  case Mul => "*"
	  case Div => "/"
	  case And => "&"
	  case Or => "|"
	  case Equal => "="
	  case Lte => "<="
	}
	
	printNode(myLbl, sym)
	printEdges(myLbl, List(e1Lbl, e2Lbl))
	myLbl
      }
      case If(e, t1, t2) => {
	val guardLbl = output(e)
	val c1Lbl = output(t1)
	val c2Lbl = output(t2)
	val myLbl = getid
	
	printNode(myLbl, "if")
	printEdges(myLbl, List(guardLbl, c1Lbl, c2Lbl))
	myLbl
      }
      case In(typ) => {
	val myLbl = getid
	val ts = typ match {
	  case NumT => "num"
	  case StrT => "str"
	}
	printNode(myLbl, "input " + ts)
	myLbl
      }
      case Call(f, es) => {
	val lbls = es map output
	val myLbl = getid
	
	printNode(myLbl, f + "(...)")
	printEdges(myLbl, lbls)
	myLbl
      }
      case Block(vds, t) => {
	val lbls = (vds map output) ::: List(output(t))
	val myLbl = getid
	
	printNode(myLbl, "block", true)
	printEdges(myLbl, lbls)
	myLbl
      }
      case FunctionDef(Var(f), _, t) => {
	val bodyLbl = output(t)
	val myLbl = getid

	printNode(myLbl, "def " + f, true)
	printEdges(myLbl, List(bodyLbl))
	myLbl
      }
      case VarBind(Var(x), e2) => {
	val rhsLbl = output(e2)
	val myLbl = getid
	
	printNode(myLbl, x + " =")
	printEdges(myLbl, List(rhsLbl))
	myLbl
      }
    }
    
    out.println( "digraph AST {" )
    output(ast)
    out.println( "}" )
    out.close()
  }
}

//---------- PARSER ----------

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._

object ParseL extends StandardTokenParsers with PackratParsers {
  type P[T] = PackratParser[T]

  // reserved keywords
  lexical.reserved += ( "var", "if", "else", "while", "true",
		       "false", "input", "output", "unit",
		       "num", "str", "in", "def", "sprout", "commit")

  lexical.delimiters += ( "+", "-", "*", "/", "!", "&", "|", "=",
			 "<=", "{", "}", "(", ")", ":=", ";", ",",
			 "<<", ">>", "=>" )
  
  // for debugging the parser: modify each rule you want to trace by
  // changing '= <pattern>' to '= "name" !!! <pattern>'
  //
  // turn off the debugging either by removing the modifications or
  // changing the !!! method to return p instead of log(p)(name)
  implicit def toLogged(name:String) = new { 
    def !!![T](p:P[T]) = p //log(p)(name)
  }

  // take the program as a string and return the corresponding AST
  // (or exit with an error message)
  def getAST(program:String) = {
    // strip out comments
    val commentR = """<<((>?[^>]+)*)>>""".r
    val prog = commentR.replaceAllIn(program, "")

    // parse the program
    val lexer = new lexical.Scanner(prog)
    val result = phrase(ProgramP)(lexer)
    
    // return result or a useful error message
    result match {
      case Success(ast,_) => ast
      case NoSuccess(msg,next) => { 
	println("Parse error: " + msg)
	println("At line " + next.pos.line + ", column " + next.pos.column)
	println(next.pos.longString)
	sys.exit(1) 
      }
    }
  }
  
  // programs
  lazy val ProgramP: P[Program] = (FunctionDefP*) ~ TermP ^^
  { case fds ~ t => Program(fds, t) }

  // terms (seqP promoted here for precedence issues)
  lazy val TermP: P[Term] = seqP

  lazy val seqP: P[Term] = "seq" !!! rep1sep((CmdP | ExpP), ";") ^^
  (_.reduceLeft(Seq(_,_)))

  // commands
  lazy val CmdP: P[Cmd] = ( assignP | whileP | outputP | sproutP | commitP)

  // expressions (factored to E for precedence issues)
  lazy val ExpP: P[Exp] = ( binopP | E )

  // expressions
  lazy val E: P[Exp] = (
      callP
    | blockP                        
    | ifP                           
    | notP
    | inputP
    | numP
    | boolP
    | strP
    | unitP
    | varP
    | accessP
    | "(" ~> ExpP <~ ")"
  )

  // assignment
  lazy val assignP: P[Assign] = "assign" !!! varP ~ (":=" ~> ExpP) ^^
  { case x ~ rhs => Assign(x, rhs) }
  
  // while
  lazy val whileP: P[While] = "while" !!! "while" ~ "(" ~> ExpP ~ (")" ~> (("{" ~> TermP <~ "}") | CmdP | ExpP)) ^^
  { case guard ~ body => While(guard, body) }

  // output
  lazy val outputP: P[Out] = "output" !!! "output" ~> ExpP ^^ (Out)

  // integer
  lazy val numP: P[Num] = "num" !!! (
      numericLit ^^ ((n:String) => Num(BigInt(n)))
    | "-" ~> numericLit ^^ ((n:String) => Num(-BigInt(n)))
  )

  // boolean
  lazy val boolP: P[Bool] = "bool" !!! (
      "true"  ^^^ Bool(true)
    | "false" ^^^ Bool(false)
  )

  // string
  lazy val strP: P[Str] = "string" !!! stringLit ^^ (Str(_))

  // unit
  lazy val unitP: P[NotUnit] = "unit" !!! ("unit" ^^^ NotUnit())

  // variable
  lazy val varP: P[Var] = "var" !!! ident ^^ (Var)

  // negation
  lazy val notP: P[Not] = "not" !!! "!" ~> E ^^ (Not)

  // binary operations
  lazy val binopP: P[BinOp] = "binop" !!! E ~ bopP ~ ExpP ^^
  { case e1 ~ bop ~ e2 => BinOp(bop, e1, e2) }
  
  // binary operators
  lazy val bopP: P[Bop] = (
      "+" ^^^ Add
    | "-" ^^^ Sub
    | "*" ^^^ Mul
    | "/" ^^^ Div
    | "&" ^^^ And
    | "|" ^^^ Or
    | "=" ^^^ Equal
    | "<=" ^^^ Lte
  )

  // if
  lazy val ifP: P[If] = "if" !!! "if" ~ "(" ~> ExpP ~ (")" ~> (("{" ~> TermP <~ "}") | CmdP | ExpP)) ~ opt("else" ~> (("{" ~> TermP <~ "}") | CmdP | ExpP)) ^^
  { 
    case guard ~ tT ~ tFo => 
      tFo match { 
	case Some(tF) => If(guard, tT, tF) 
        case None => If(guard, tT, NotUnit())
      }
  }

  // input
  lazy val inputP: P[In] = "input" !!! "input" ~> typP ^^ (In)
  
  // types
  lazy val typP: P[InputType] = (
      "num"  ^^^ NumT
    | "str"  ^^^ StrT
  )

  // function call
  lazy val callP: P[Call] = "call" !!! varP ~ ("(" ~> repsep(ExpP, ",") <~ ")") ^^
  { case fun ~ args => Call(fun, args) }

  // Sprout
  lazy val sproutP: P[Sprout] = "sprout" !!! opt(varP) ~ ("." ~ "sprout" ~ "(" ~> varP <~ ")") ^^
  { case w1 ~ w2 => w1 match {
	    case Some(v) => Sprout(v, w2)
	    case None    => Sprout(Var("root"), w2) 
	  }
  }

  // commit
  lazy val commitP: P[Commit] = "commit" !!! varP <~ ("." ~ "commit") ^^
  { case w => Commit(w) }

  // object field access
  lazy val accessP: P[Access] = "access" !!! varP ~ ("." ~> varP) <~ not(":=") ^^
  { case rec ~ fld => Access(rec, fld) }

  // field update
  lazy val updateP: P[Update] = "update" !!! varP ~ ("." ~> varP) ~ (":=" ~> ExpP) ^^
  { case rec ~ fld ~ rhs => Update(rec, fld, rhs) }

  // block
  lazy val blockP: P[Block] = "var" !!! "var" ~> rep1sep(vbindP, ",") ~ ("in" ~> (("{" ~> TermP <~ "}") | TermP)) ^^
  { case vbs ~ t => Block(vbs, t) }

  // variable binding
  lazy val vbindP: P[VarBind] = "vbind" !!! varP ~ ("=" ~> ExpP) ^^
  { case x ~ e => VarBind(x, e) }

  // function def
  lazy val FunctionDefP: P[FunctionDef] = "def" !!! "def" ~> varP ~ ("(" ~> repsep(varP, ",") <~ ")" ~ "=>" ~ "{") ~ TermP <~ "}" ^^
  { case f ~ prms ~ body => FunctionDef(f, prms, body) }
}
