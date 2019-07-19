import java.nio.file.{Files, Path, Paths}
import java.util.Comparator

scalaVersion := "2.12.7"

/* Task to create symbolic links to link the Viper modules.
 * Is not supported on Windows systems.
 * TODO: try to integrate it in the build. */
lazy val linkViper = taskKey[Unit]("Create symbolic links to link the Viper modules")

lazy val hre = project in file("hre")
lazy val silicon = ProjectRef(uri("hg:https://bitbucket.org/viperproject/silicon/"), "silicon")
lazy val carbon = ProjectRef(uri("hg:https://bitbucket.org/viperproject/carbon/"), "carbon")
lazy val silver = ProjectRef(uri("hg:https://bitbucket.org/viperproject/silver/"), "silver")

lazy val viper_api = (project in file("."))
  .dependsOn(silver)
  .dependsOn(silicon, carbon)
  .dependsOn(hre)
  .settings(
    name := "viper-api",
    organization := "vercors",
    version := "1.0-SNAPSHOT",

    linkViper := {
      val log = streams.value.log
      val carbonLink = (baseDirectory in carbon).value.toPath.resolve("silver")
      val siliconLink = (baseDirectory in silicon).value.toPath.resolve("silver")
      val silverPath = (baseDirectory in silver).value.toPath
      log.info(carbonLink.toString)
      log.info(siliconLink.toString)
      log.info(silverPath.toString)
      try {
        Files.walk(carbonLink).sorted(Comparator.reverseOrder()).forEach((p: Path) => p.toFile.delete())
        Files.createSymbolicLink(carbonLink, silverPath)
        Files.walk(siliconLink).sorted(Comparator.reverseOrder()).forEach((p: Path) => p.toFile.delete())
        Files.createSymbolicLink(siliconLink, silverPath)
      } catch {
        case e: Exception => {
          println("Unable to find or create symbolic links for Viper. Please create the links manually as explained in vercors/viper/README.md")
          e.printStackTrace()
        }
      }
    },

    linkViper := (linkViper triggeredBy update).value,

    assemblyMergeStrategy in assembly := {
      case "logback.xml" => MergeStrategy.first
      case x =>
        val oldStrategy = (assemblyMergeStrategy in assembly).value
        oldStrategy(x)
    }
  )
