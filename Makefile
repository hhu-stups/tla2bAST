# Makefile as documentation on how to build the TLA2B.jar file
# This file should then be put into ProB's lib folder
# This file is for documentation, for users not familiar with gradle
JAR=tla2bAST-1.2.2-SNAPSHOT-all.jar
build/libs/$(JAR): src/main/java/de/tla2b/*/*.java src/main/java/de/tla2b/*.java src/main/java/de/tla2bAst/*.java build.gradle
	@echo "Building TLA2B.jar"
	gradle shadowJar
install: build/libs/$(JAR)
	@echo "Copying the TLA2B jar file to default location of prob_prolog"
	cp build/libs/$(JAR) ../../prob_prolog/lib/TLA2B.jar
FILE = src/test/resources/examples/instance/Counter/Counter
test: build/libs/$(JAR)
	@echo "Running a simple test using the TLA2B jar file"
	java -jar build/libs/$(JAR) $(FILE).tla
	@echo "Checking if probcli can load the generate .prob file"
	probcli $(FILE).prob -ppf user_output
