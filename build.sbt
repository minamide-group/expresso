name := "sst-composition"

version := "0.1"

scalaVersion := "2.13.3"

libraryDependencies ++= Seq(
 "org.typelevel" %% "cats-core" % "2.1.1",
 "org.scalatest" %% "scalatest" % "3.1.0" % "test"
)

fork in run := true
fork in Test := true
cancelable in Global := true

scalacOptions ++= Seq(
  "-encoding",
  "utf8",
  "-Xfatal-warnings",
  "-deprecation",
  "-unchecked",
  "-language:implicitConversions",
  "-language:higherKinds",
  "-language:existentials",
  "-language:postfixOps"
)
