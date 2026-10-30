// Stainless verifies src/main on every `compile`; src/test is plain Scala run by ScalaCheck.
lazy val verify = taskKey[Unit]("Verifies src/main with Stainless; fails unless every verification condition is valid")

lazy val rooms = project
  .in(file("."))
  .enablePlugins(StainlessPlugin)
  .settings(
    scalaVersion := "3.10.1-RC1-bin-20260903-e1f9361-NIGHTLY",
    libraryDependencies ++= Seq(
      "org.xerial" % "sqlite-jdbc" % "3.46.1.3",
      "org.scalacheck" %% "scalacheck" % "1.18.1" % Test
    ),
    // Tests are plain Scala run by ScalaCheck; they use the Stainless library as compiled for Compile.
    Test / stainlessEnabled := false,
    Test / managedSources := Nil,
    Test / scalacOptions += "-experimental", // main is compiled with Stainless's experimental qualified types
    Test / fork := true,
    // The Stainless sbt plugin prints its report but does not fail the build on an invalid or unknown verification
    // condition. `verify` recompiles src/main, so the report is fresh, and fails unless every condition is valid.
    verify := Def.sequential(
      Def.task(IO.delete(Seq((Compile / classDirectory).value, (Compile / compileAnalysisFile).value))),
      Compile / compile,
      Def.task {
        val out = (Compile / compile / streams).value.cacheDirectory / "out"
        val totals = IO.readLines(out).map(_.replaceAll("\u001b\\[[0-9;]*m", "")).filter(_.contains("total:"))
        val Summary = """.*total:\s*(\d+)\s+valid:\s*(\d+).*""".r
        totals.lastOption match {
          case Some(Summary(total, valid)) if total == valid =>
            streams.value.log.info(s"Stainless: all $total verification conditions valid")
          case Some(line) => sys.error(s"Stainless: not every verification condition is valid:\n$line")
          case None       => sys.error(s"Stainless: no verification report found in $out")
        }
      }
    ).value
  )
