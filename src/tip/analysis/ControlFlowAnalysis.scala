package tip.analysis

import tip.ast.{AAssignStmt, AIdentifier, AProgram, AstNode, DepthFirstAstVisitor, _}
import tip.solvers.SimpleCubicSolver
import tip.util.Log
import tip.ast.AstNodeData.{AstNodeWithDeclaration, DeclarationData}

import scala.language.implicitConversions

/**
  * Control flow analysis.
  */
class ControlFlowAnalysis(program: AProgram)(implicit declData: DeclarationData)
    extends DepthFirstAstVisitor[Unit]
    with Analysis[Map[AstNode, Set[AFunDeclaration]]] {

  val log = Log.logger[this.type]()

  case class Decl(fun: AFunDeclaration) {
    override def toString = s"${fun.name}:${fun.loc}"
  }

  case class AstVariable(n: AstNode) {
    override def toString: String = n match {
      case fun: AFunDeclaration => s"${fun.name}:${fun.loc}"
      case _ => n.toString
    }
  }

  private val solver = new SimpleCubicSolver[AstVariable, Decl]

  val allFunctions: Set[AFunDeclaration] = program.funs.toSet

  NoPointers.assertContainsProgram(program)
  NoRecords.assertContainsProgram(program)

  /**
    * @inheritdoc
    */
  def analyze(): Map[AstNode, Set[AFunDeclaration]] = {
    visit(program, ())
    val sol = solver.getSolution
    log.info(s"Solution is:\n${sol.map { case (k, v) => s"  \u27E6$k\u27E7 = {${v.mkString(",")}}" }.mkString("\n")}")
    sol.map(vardecl => vardecl._1.n -> vardecl._2.map(_.fun))
  }

  /**
    * Generates the constraints for the given sub-AST.
    * @param node the node for which it generates the constraints
    * @param arg unused for this visitor
    */
  def visit(node: AstNode, arg: Unit): Unit = {

    /**
      * Get the declaration if the supplied AstNode is an identifier,
      * which might be a variable declaration or a function declaration.
      * It returns the node itself, otherwise.
      */
    def decl(n: AstNode): AstNode = n match {
      case id: AIdentifier => id.declaration
      case _ => n
    }

    implicit def toVar(n: AstNode): AstVariable = AstVariable(n)

    node match {
      case fun: AFunDeclaration => solver.addConstantConstraint(Decl(fun), fun)
      case AAssignStmt(id: AIdentifier, e, _) => solver.addSubsetConstraint(decl(e), decl(id))
      case ACallFuncExpr(targetFun: AIdentifier, args, _) if decl(targetFun).isInstanceOf[AFunDeclaration] =>
        targetFun.declaration match {
          case AFunDeclaration(_, params, stmts, _) =>
            params.zip(args).foreach(pa => solver.addSubsetConstraint(decl(pa._2), pa._1))
            solver.addSubsetConstraint(decl(stmts.ret.exp), node)
        }
      case ACallFuncExpr(targetFun, args, _) =>
        allFunctions
          .filter(_.params.length == args.length)
          .foreach(f => {
            f.params.zip(args).foreach(pa => solver.addConditionalConstraint(Decl(f), decl(targetFun), decl(pa._2), pa._1))
            solver.addConditionalConstraint(Decl(f), decl(targetFun), decl(f.stmts.ret.exp), node)
          })
      case _ =>
    }
    visitChildren(node, ())
  }
}
