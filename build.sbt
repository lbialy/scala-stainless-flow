// Stainless verifies src/main on every `compile`; src/test is plain Scala run by ScalaCheck.
val laraScalaVersion = "3.10.1-RC1-bin-20260903-e1f9361-NIGHTLY"

lazy val verify = taskKey[Unit]("Verifies src/main with Stainless; fails unless every verification condition is valid")
lazy val flow = inputKey[Unit](
  "The statements and the developer's decisions: tree | status | show NAME | review | accept NAME... --as WHO | reject"
)

lazy val rooms = project
  .in(file("."))
  .enablePlugins(StainlessPlugin)
  .settings(
    scalaVersion := laraScalaVersion,
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
    ).value,
    // Reads the statements from the TASTy of src/main (which still holds every contract and ghost block).
    flow := Def.inputTaskDyn {
      val args      = complete.DefaultParsers.spaceDelimited("<command>").parsed
      val classpath = (Compile / fullClasspath).value.files.mkString(java.io.File.pathSeparator)
      val cpFile    = target.value / "flow-classpath.txt"
      IO.write(cpFile, classpath)
      val root    = baseDirectory.value
      val classes = (Compile / classDirectory).value
      val sources = (Compile / unmanagedSourceDirectories).value.mkString(java.io.File.pathSeparator)
      (review / Compile / runMain).toTask(
        s" flow.review.Main --title Rooms --root $root --classes $classes --sources $sources --classpath-file $cpFile -- ${args.mkString(" ")}"
      )
    }.evaluated
  )

// The `flow` tool: plain Scala, no Stainless, on the same compiler so it can read the TASTy above.
lazy val review = project
  .in(file("review"))
  .settings(
    scalaVersion := laraScalaVersion,
    scalaOrganization := "ch.epfl.lara",
    excludeDependencies ++= Seq(
      ExclusionRule("org.scala-lang", "scala3-library_3"),
      ExclusionRule("org.scala-lang", "scala3-compiler_3"),
      ExclusionRule("org.scala-lang", "scala-library")
    ),
    libraryDependencies ++= Seq(
      "ch.epfl.lara" %% "scala3-tasty-inspector" % laraScalaVersion,
      "com.lihaoyi" %% "upickle" % "4.1.0"
    ),
    run / fork := true,
    run / baseDirectory := (ThisBuild / baseDirectory).value, // TASTy positions are relative to the build root
    run / connectInput := true, // ssh-keygen may ask for the key's passphrase
    run / outputStrategy := Some(StdoutOutput)
  )
