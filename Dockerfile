FROM openjdk:11-jre

ENV Z3_VERSION "4.8.8"

WORKDIR /tmp
RUN curl -LO https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-ubuntu-16.04.zip
RUN unzip z3-${Z3_VERSION}-x64-ubuntu-16.04.zip
RUN cp z3-${Z3_VERSION}-x64-ubuntu-16.04/bin/libz3* /usr/lib
RUN rm -rf z3*

WORKDIR /app
COPY ./target/scala-2.13/expresso-assembly-0.3.0-SNAPSHOT.jar ./expresso.jar

# docker run -v $(pwd)/constraints/bench:/workdir -it IMAGE CONSTRAINT STRATEGY
WORKDIR /workdir
ENTRYPOINT [ "java", "-jar", "/app/expresso.jar" ]
