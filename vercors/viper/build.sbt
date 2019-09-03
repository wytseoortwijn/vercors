import java.nio.file.{Files, Path, Paths}
import java.net.URL
import java.util.Comparator

scalaVersion := "2.12.7"

/* Task to create symbolic links to link the Viper modules.
 * Is not supported on Windows systems.
 * TODO: try to integrate it in the build. */
lazy val linkViper = taskKey[Unit]("Create symbolic links to link the Viper modules")

lazy val hre = project in file("hre")

lazy val silver_ref = ProjectRef(uri("hg:https://bitbucket.org/viperproject/silver#1e36f47912275ee796a5af38d0eabb5fc83d1c71"), "silver")
lazy val carbon_ref = ProjectRef(uri("hg:https://bitbucket.org/viperproject/carbon#4343ff7170839272392b94b4fe1ef4eb7712d598"), "carbon")
lazy val silicon_ref = ProjectRef(uri("hg:https://bitbucket.org/viperproject/silicon#8d3234adca7278e90f594ac760518cafb26b0404"), "silicon")

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
