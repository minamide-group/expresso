name := "expresso"

version := "0.3.0-SNAPSHOT"

scalaVersion := "2.13.3"

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "3.1.0" % "test",
  "com.typesafe.scala-logging" %% "scala-logging" % "3.9.2",
  "ch.qos.logback" % "logback-classic" % "1.2.3"
)

fork in run := true
fork in Test := true
cancelable in Global := true

scalacOptions ++= Seq(
  "-encoding",
  "utf8",
  "-Xfatal-warnings",
  "-deprecation",
  "-feature",
  "-unchecked",
  "-language:implicitConversions",
  "-language:higherKinds",
  "-language:existentials",
  "-language:postfixOps"
)
