import java.nio.file.{Files, Path, Paths}
import java.util.Comparator

scalaVersion := "2.12.7"

/* Task to create symbolic links to link the Viper modules.
 * Is not supported on Windows systems.
 * TODO: try to integrate it in the build. */
lazy val linkViper = taskKey[Unit]("Create symbolic links to link the Viper modules")

lazy val hre = project in file("hre")

lazy val silver_ref = ProjectRef(uri("hg:https://bitbucket.org/viperproject/silver"), "silver")
lazy val carbon_ref = ProjectRef(uri("hg:https://bitbucket.org/viperproject/carbon"), "carbon")
lazy val silicon_ref = ProjectRef(uri("hg:https://bitbucket.org/viperproject/silicon"), "silicon")

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
