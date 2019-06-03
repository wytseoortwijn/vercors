import java.nio.file.{Files, Paths}

scalaVersion := "2.12.7"

/* Task to create symbolic links to link the Viper modules.
 * Is not supported on Windows systems.
 * TODO: try to integrate it in the build. */
lazy val linkViper = taskKey[Unit]("Create symbolic links to link the Viper modules")
linkViper := {
  val carbonLink = Paths.get("carbon/silver")
  val siliconLink = Paths.get("silicon/silver")
  val silverPath = Paths.get("silver")
  try {
    if(!carbonLink.toFile().exists()){
      Files.createSymbolicLink(carbonLink, silverPath)
    }
    if(!siliconLink.toFile().exists()){
      Files.createSymbolicLink(siliconLink, silverPath)
    }
  }catch {
    case e: Exception => println("Unable to find or create symbolic links for Viper. Please create the links manually as explained in vercors/viper/README.md")
  }
}

lazy val hre = (project in file("hre"))

lazy val silver = (project in file("silver"))
lazy val silicon = (project in file("silicon"))
lazy val carbon = (project in file("carbon"))

lazy val viper_api = (project in file("."))
  .dependsOn(silicon, carbon, silver)
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
