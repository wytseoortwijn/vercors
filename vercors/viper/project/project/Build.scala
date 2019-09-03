import sbt._
import Keys._

object PatchBuild extends Build {
  override def buildLoaders = BuildLoader.transform(patchDependencies) :: Nil

  def patchTransformers: BuildLoader.TransformInfo => BuildUnit = {

  }
}