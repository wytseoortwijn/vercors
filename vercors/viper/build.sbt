import java.nio.file.{Files, Path, Paths}
import java.net.URL
import java.util.Comparator
import sbt.internal._

val silver_url = uri("hg:https://bitbucket.org/viperproject/silver#1e36f47912275ee796a5af38d0eabb5fc83d1c71")
val carbon_url = uri("hg:https://bitbucket.org/viperproject/carbon#4343ff7170839272392b94b4fe1ef4eb7712d598")
val silicon_url = uri("hg:https://bitbucket.org/viperproject/silicon#8d3234adca7278e90f594ac760518cafb26b0404")

scalaVersion := "2.12.7"

/*
buildDepdendencies.classpath contains the mapping from project to a list of its dependencies. The viper projects silver,
silicon and carbon specify their dependencies as a regular sbt subproject: they expect a symlink in the project root to
the relevant project. Instead, we replace those dependencies by a reference to the repository as above. So e.g.
"the silver project at hg:carbon" becomes "the silver project at hg:silver". All other dependencies are left alone.
 */
buildDependencies in Global := {
  val log = sLog.value
  val oldDeps = (buildDependencies in Global).value
  def fixDep(dep: ClasspathDep[ProjectRef]): ClasspathDep[ProjectRef] = dep.project.project match {
    case "silver" =>
      ResolvedClasspathDependency(ProjectRef(silver_url, "silver"), dep.configuration)
    case "silicon" =>
      ResolvedClasspathDependency(ProjectRef(silicon_url, "silicon"), dep.configuration)
    case "carbon" =>
      ResolvedClasspathDependency(ProjectRef(carbon_url, "carbon"), dep.configuration)
    case _ =>
      dep
  }
  val newDeps = for((proj, deps) <- oldDeps.classpath) yield (proj, deps map fixDep)
  BuildDependencies(newDeps, oldDeps.aggregate)
}

lazy val hre = project in file("hre")

lazy val silver_ref = ProjectRef(silver_url, "silver")
lazy val carbon_ref = ProjectRef(carbon_url, "carbon")
lazy val silicon_ref = ProjectRef(silicon_url, "silicon")

lazy val viper_api = (project in file("."))
  .dependsOn(silver_ref, silicon_ref, carbon_ref)
  .dependsOn(hre)
  .settings(
    name := "viper-api",
    organization := "vercors",
    version := "1.0-SNAPSHOT",

    assemblyMergeStrategy in assembly := {
      case "logback.xml" => MergeStrategy.first
      case x =>
        val oldStrategy = (assemblyMergeStrategy in assembly).value
        oldStrategy(x)
    }
  )
