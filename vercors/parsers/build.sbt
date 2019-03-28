enablePlugins(Antlr4Plugin)

lazy val parsers = (project in file(".")).settings(
    // antlr4Version in Antlr4 := "4.5.3",
    antlr4PackageName in Antlr4 := Some("vct.antlr4.generated"),
    antlr4GenVisitor in Antlr4 := true,
    antlr4LibDirectory in Antlr4 := Some((unmanagedBase in Compile).value / "antlr4")
)
