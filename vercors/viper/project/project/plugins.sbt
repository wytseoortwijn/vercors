lazy val root = (project in file(".")).dependsOn(patch_plugin)
lazy val patch_plugin = RootProject(file("patch_plugin"))