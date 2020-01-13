build/libs/TLA2B.jar: src/main/java/de/tla2b/*/*.java src/main/java/de/tla2b/*.java
	gradle createJar
install: build/libs/TLA2B.jar
	cp build/libs/TLA2B.jar ../../prob_prolog/lib/

