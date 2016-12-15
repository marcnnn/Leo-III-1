package leo.datastructures.tptp

object Commons {

  // Files
  sealed case class TPTPInput(inputs: Seq[Either[AnnotatedFormula, Include]]) {
    def getIncludes:Seq[Include] = inputs.filter(x => x.isRight).map(_.right.get)
    def getIncludeCount: Int = getIncludes.size
    def getFormulae:Seq[AnnotatedFormula] = inputs.filter(x => x.isLeft).map(_.left.get)
    def getFormulaeCount: Int = getFormulae.size
  }

  // Formula records
  sealed abstract class AnnotatedFormula(val name: Name, val role: Role,val annotations: Annotations) {
    type FormulaType
    def f: FormulaType

    lazy val rep = "(" + name + "," + role + "," + "(" + f.toString + ")" + annoToString(annotations) + ")."

    /**
      * Collects all Function symbols of the formula.
      * Usefull for relevance filtering
      * @return All function symbols of the formula
      */
    def function_symbols : Set[String]
  }
  case class TPIAnnotated(override val name: Name,override val role: Role,formula: fof.Formula,override val annotations: Annotations) extends AnnotatedFormula(name, role, annotations) {
    override type FormulaType = fof.Formula
    override def f = formula

    override def toString = "tpi" + rep

    override val function_symbols : Set[String] = formula.function_symbols
  }
  case class THFAnnotated(override val name: Name, override val role: Role, formula: thf.Formula,override val annotations: Annotations) extends AnnotatedFormula(name, role, annotations) {
    override type FormulaType = thf.Formula
    override def f = formula

    override def toString = "thf" + rep
    override val function_symbols : Set[String] = formula.function_symbols
  }
  case class TFFAnnotated(override val name: Name, override val role: Role, formula: tff.Formula, override val annotations: Annotations) extends AnnotatedFormula(name, role, annotations) {
    override type FormulaType = tff.Formula
    override def f = formula

    override def toString = "tff" + rep
    override val function_symbols : Set[String] = formula.function_symbols
  }
  case class FOFAnnotated(override val name: Name, override val role: Role, formula: fof.Formula, override val annotations: Annotations) extends AnnotatedFormula(name, role, annotations) {
    override type FormulaType = fof.Formula
    override def f = formula

    override def toString = "fof" + rep
    override val function_symbols : Set[String] = formula.function_symbols
  }
  case class CNFAnnotated(override val name: Name, override val role: Role, formula: cnf.Formula,override val annotations: Annotations) extends AnnotatedFormula(name, role, annotations) {
    override type FormulaType = cnf.Formula
    override def f = formula

    override def toString = "cnf" + rep
    override val function_symbols : Set[String] = formula.function_symbols
  }

  type Annotations = Option[(Source, Seq[GeneralTerm])]
  type Role = String

  // First-order atoms
  sealed abstract class AtomicFormula {
    def function_symbols : Set[String]
  }
  case class Plain(data: Func) extends AtomicFormula {
    override def toString = data.toString

    override val function_symbols: Set[String] = data.function_symbols
  }
  case class DefinedPlain(data: DefinedFunc) extends AtomicFormula {
    override def toString = data.toString

    override val function_symbols: Set[String] = data.function_symbols
  }
  case class Equality(left: Term, right: Term) extends AtomicFormula {
    override def toString = left.toString + " = " + right.toString

    override val function_symbols: Set[String] = left.function_symbols union right.function_symbols
  }
  case class SystemPlain(data: SystemFunc) extends AtomicFormula {
    override def toString = data.toString

    override val function_symbols: Set[String] = data.function_symbols
  }

  // First-order terms
  sealed abstract class Term {
    def function_symbols : Set[String]
  }
  case class Func(name: String, args: Seq[Term]) extends Term {
    override def toString = funcToString(name, args)

    override val function_symbols: Set[String] =  args.flatMap(_.function_symbols).toSet + name
  }
  case class DefinedFunc(name: String, args: Seq[Term]) extends Term {
    override def toString = funcToString(name, args)
    override val function_symbols: Set[String] =  args.flatMap(_.function_symbols).toSet + name
  }
  case class SystemFunc(name: String, args: Seq[Term]) extends Term {
    override def toString = funcToString(name, args)
    override val function_symbols: Set[String] =  args.flatMap(_.function_symbols).toSet + name
  }
  case class Var(name: Variable) extends Term {
    override def toString = name.toString
    override val function_symbols: Set[String] =  Set(name)
  }
  case class NumberTerm(value: Number) extends Term {
    override def toString = value.toString
    override val function_symbols: Set[String] =  Set()
  }
  case class Distinct(data: String) extends Term {
    override def toString = data.toString
    override val function_symbols: Set[String] =  Set()
  }
  case class Cond(cond: tff.LogicFormula, thn: Term, els: Term) extends Term {
    override def toString = "$ite_t(" + List(cond,thn,els).mkString(",") + ")"
    override val function_symbols: Set[String] =  cond.function_symbols union thn.function_symbols union els.function_symbols
  } // Cond used by TFF only
  // can Let be modeled like this?
  case class Let(let: tff.LetBinding, in: Term) extends Term {
    override def function_symbols: Set[String] = let.function_symbols union in.function_symbols
  } // Let used by TFF only

  type Variable = String

  sealed abstract class Number
  case class IntegerNumber(value: Integer) extends Number {
    override def toString = value.toString
  }
  case class DoubleNumber(value: Double) extends Number
  case class RationalNumber(p: Integer, q: Integer) extends Number {
    override def toString = p.toString + "/" + q.toString
  }

  // System terms

  // General purpose things
  type Source = GeneralTerm

  // Include directives
  type Include = (String, Seq[Name])

  // Non-logical data (GeneralTerm, General data)
  sealed case class GeneralTerm(term: Seq[Either[GeneralData, Seq[GeneralTerm]]]) {
    override def toString = term.map(gt2String).mkString(":")

    def gt2String(in: Either[GeneralData, Seq[GeneralTerm]]): String = in match {
      case Left(data) => data.toString
      case Right(termList) => "[" + termList.mkString(",") +"]"
    }

  }

  sealed abstract class GeneralData
  case class GWord(gWord: String) extends GeneralData {
    override def toString = gWord
  }
  case class GFunc(name: String, args: Seq[GeneralTerm]) extends GeneralData {
    override def toString = funcToString(name, args)
  }
  case class GVar(gVar: Variable) extends GeneralData {
    override def toString = gVar.toString
  }
  case class GNumber(gNumber: Number) extends GeneralData {
    override def toString = gNumber.toString
  }
  case class GDistinct(data: String) extends GeneralData {
    override def toString = data
  }
  case class GFormulaData(data: FormulaData) extends GeneralData {
    override def toString = data.toString
  }

  sealed abstract class FormulaData
  case class THFData(formula: thf.Formula) extends FormulaData {
    override def toString = "$thf(" + formula.toString + ")"
  }
  case class TFFData(formula: tff.Formula) extends FormulaData {
    override def toString = "$tff(" + formula.toString + ")"
  }
  case class FOFData(formula: fof.Formula) extends FormulaData {
    override def toString = "$fof(" + formula.toString + ")"
  }
  case class CNFData(formula: cnf.Formula) extends FormulaData {
    override def toString = "$cnf(" + formula.toString + ")"
  }
  case class FOTData(term: Term) extends FormulaData {
    override def toString = "$fot(" + term.toString + ")"
  }

  // General purpose
  type Name = String


  ///////// String representation functions ///////////
  def funcToString(name:String, args: Seq[Any]) = args match {
    case Seq()     => name
    case _          => name + "(" + args.mkString(",") + ")"
  }

  def annoToString(anno: Option[(Source, Seq[GeneralTerm])]) = anno match {
    case None => ""
    case Some((src, termList)) => "," + src.toString + ",[" + termList.mkString(",") + "]"
  }

  def typedVarToString(input: (Variable,Option[Any])) = input match {
    case (v, None) => v.toString
    case (v, Some(typ)) => v.toString + " : " + typ.toString
  }
}