package cubical

import scala.io.StdIn
import scala.io.Source
import java.io.File

/** REPL and script interpreter for cubicaltt-scala.
 *  Usage:
 *    scala-cli run . -- file.ctt    (interpret file)
 *    scala-cli run .                (start REPL)
 */
object Main:
  def main(args: Array[String]): Unit =
    if args.isEmpty then
      repl()
    else
      interpretFile(args(0))

  def repl(): Unit =
    println("cubicaltt-scala — Cubical Type Theory in Scala 3 🐎✨")
    println("Type :quit to exit, :help for commands")
    println("="*55)
    
    var ctx = TCtx.empty
    var env = Env.empty
    var running = true
    
    while running do
      print("cubical> ")
      val input = StdIn.readLine()
      
      if input == null || input == ":quit" then
        running = false
      else if input == ":help" then
        printHelp()
      else if input.startsWith(":load ") then
        val file = input.drop(6).trim
        loadFile(file, ctx, env) match
          case Some((newCtx, newEnv)) =>
            ctx = newCtx
            env = newEnv
          case None => ()
      else if input.trim.nonEmpty then
        evalLine(input, ctx, env)
    
    println("Goodbye! 🐎✨")
  
  def printHelp(): Unit =
    println("""
Commands:
  :quit           Exit the REPL
  :help           Show this help
  :load <file>    Load and evaluate a .ctt file
  
Enter any term to parse and evaluate it.
""")
  
  def evalLine(input: String, ctx: TCtx, env: Env): Unit =
    Parser.parseAll(Parser.term, input) match
      case Parser.Success(term, _) =>
        try
          val value = Eval.eval(term, env)
          println(s"  => $value")
        catch
          case e: Exception => println(s"  Error: ${e.getMessage}")
      case Parser.Failure(msg, _) =>
        println(s"  Parse error: $msg")
      case Parser.Error(msg, _) =>
        println(s"  Parse error: $msg")
  
  def loadFile(path: String, ctx: TCtx, env: Env): Option[(TCtx, Env)] =
    val file = File(path)
    if !file.exists() then
      println(s"  File not found: $path")
      None
    else
      println(s"  Loading $path...")
      // TODO: Parse and type-check declarations
      println(s"  (File loading not yet implemented)")
      Some((ctx, env))
  
  def interpretFile(path: String): Unit =
    println(s"Interpreting $path...")
    loadFile(path, TCtx.empty, Env.empty)
    println("Done.")

end Main

