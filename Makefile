# Makefile as documentation on how to build the TLA2B.jar file
# This file should then be put into ProB's lib folder
# This file is for documentation, for users not familiar with gradle
build/libs/TLA2B.jar: src/main/java/de/tla2b/*/*.java src/main/java/de/tla2b/*.java src/main/java/de/tla2bAst/*.java build.gradle
	@echo "Building TLA2B.jar"
	gradle shadowJar
install: build/libs/TLA2B.jar
	@echo "Copying the TLA2B jar file to default location of prob_prolog"
	cp build/libs/TLA2B.jar ../../prob_prolog/lib/
FILE = src/test/resources/examples/instance/Counter/Counter
test: build/libs/TLA2B.jar
	@echo "Running a simple test using the TLA2B jar file"
	java -jar build/libs/TLA2B.jar $(FILE).tla
	@echo "Checking if probcli can load the generate .prob file"
	probcli $(FILE).prob -ppf user_output
