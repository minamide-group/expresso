name := "sst-composition"

version := "0.1"

scalaVersion := "2.13.1"

libraryDependencies += "org.scalatest" % "scalatest_2.13" % "3.1.0" % "test"

fork in run := true
cancelable in Global := true

scalacOptions ++= Seq(
  "-encoding", "utf8", // Option and arguments on same line
  "-Xfatal-warnings",  // New lines for each options
  "-deprecation",
  "-unchecked",
  "-language:implicitConversions",
  "-language:higherKinds",
  "-language:existentials",
  "-language:postfixOps"
)