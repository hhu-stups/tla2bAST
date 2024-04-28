package de.tla2b.global;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.nio.charset.StandardCharsets;
import java.util.Properties;

final class VersionHelper {
	private VersionHelper() {
		throw new AssertionError("Utility class");
	}

	static final String VERSION;

	static {
		final Properties buildProperties = new Properties();
		final InputStream is = VersionHelper.class.getResourceAsStream("/de/tla2b/build.properties");
		if (is == null) {
			throw new AssertionError("Build properties not found, this should never happen!");
		} else {
			try (final Reader r = new InputStreamReader(is, StandardCharsets.UTF_8)) {
				buildProperties.load(r);
			} catch (final IOException e) {
				throw new AssertionError("IOException while loading build properties, this should never happen!", e);
			}
		}
		VERSION = buildProperties.getProperty("version");
	}
}
