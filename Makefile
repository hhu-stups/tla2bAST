build/libs/TLA2B.jar: src/main/java/de/tla2b/*/*.java src/main/java/de/tla2b/*.java src/main/java/de/tla2bAst/*.java build.gradle
	gradle createJar
install: build/libs/TLA2B.jar
	cp build/libs/TLA2B.jar ../../prob_prolog/lib/

test: build/libs/TLA2B.jar
	java -jar build/libs/TLA2B.jar $(FILE).tla
	probcli $(FILE).prob -ppf user_output
