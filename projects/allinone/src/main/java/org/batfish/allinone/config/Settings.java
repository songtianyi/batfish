package org.batfish.allinone.config;

import java.nio.file.Path;
import java.util.Collections;
import java.util.List;
import org.batfish.common.BaseSettings;
import org.batfish.common.BatfishLogger;
import org.batfish.common.BfConsts;
import org.batfish.common.Version;
import org.batfish.common.util.CommonUtil;

public class Settings extends BaseSettings {

   private static final String ARG_BATFISH_ARGS = "batfishargs";
   private static final String ARG_CLIENT_ARGS = "clientargs";
   private static final String ARG_COMMAND_FILE =
         org.batfish.client.config.Settings.ARG_COMMAND_FILE;
   private static final String ARG_COORDINATOR_ARGS = "coordinatorargs";
   private static final String ARG_HELP = "help";
   private static final String ARG_LOG_FILE = "logfile";
   private static final String ARG_LOG_LEVEL = "loglevel";
   private static final String ARG_RUN_CLIENT = "runclient";
   private static final String ARG_RUN_MODE = org.batfish.client.config.Settings.ARG_RUN_MODE;
   private static final String ARG_TESTRIG_DIR = org.batfish.client.config.Settings.ARG_TESTRIG_DIR;
   private static final String ARG_VERSION = "version";

   private static final String EXECUTABLE_NAME = "allinone";

   private String _batfishArgs;
   private String _clientArgs;
   private String _commandFile;
   private String _coordinatorArgs;
   private String _logFile;
   private String _logLevel;
   private List<Path> _pluginDirs;
   private boolean _runClient;
   private String _runMode;
   private String _testrigDir;

   public Settings(String[] args) throws Exception {
      super(CommonUtil.getConfig(
            BfConsts.PROP_ALLINONE_PROPERTIES_PATH,
            BfConsts.ABSPATH_CONFIG_FILE_NAME_ALLINONE, ConfigurationLocator.class));

      initConfigDefaults();

      initOptions();
      parseCommandLine(args);
   }

   public String getBatfishArgs() {
      return _batfishArgs;
   }

   public String getClientArgs() {
      return _clientArgs;
   }

   public String getCommandFile() {
      return _commandFile;
   }

   public String getCoordinatorArgs() {
      return _coordinatorArgs;
   }

   public String getLogFile() {
      return _logFile;
   }

   public String getLogLevel() {
      return _logLevel;
   }

   public List<Path> getPluginDirs() {
      return _pluginDirs;
   }

   public boolean getRunClient() {
      return _runClient;
   }

   public String getRunMode() {
      return _runMode;
   }

   public String getTestrigDir() {
      return _testrigDir;
   }

   private void initConfigDefaults() {
      // setDefaultProperty(ARG_COMMAND_FILE,
      // Paths.get(org.batfish.common.Util.getJarOrClassDir(
      // ConfigurationLocator.class).getAbsolutePath(), "default_commands")
      // .toAbsolutePath().toString());
      setDefaultProperty(ARG_HELP, false);
      setDefaultProperty(ARG_LOG_FILE, null);
      setDefaultProperty(
            ARG_LOG_LEVEL,
            BatfishLogger.getLogLevelStr(BatfishLogger.LEVEL_OUTPUT));
      setDefaultProperty(ARG_BATFISH_ARGS, "");
      setDefaultProperty(ARG_CLIENT_ARGS, "");
      setDefaultProperty(ARG_COORDINATOR_ARGS, "");
      setDefaultProperty(ARG_RUN_CLIENT, true);
      setDefaultProperty(ARG_RUN_MODE, "batch");
      setDefaultProperty(
            BfConsts.ARG_PLUGIN_DIRS,
            Collections.<String>emptyList());
      setDefaultProperty(ARG_VERSION, false);
   }

   private void initOptions() {
      addOption(ARG_COMMAND_FILE,
            "read commands from the specified command file", "cmdfile");

      addBooleanOption(ARG_HELP, "print help message and exit");

      addOption(ARG_LOG_FILE, "send output to specified log file", "logfile");

      addOption(ARG_LOG_LEVEL, "log level", "loglevel");

      addOption(ARG_BATFISH_ARGS, "arguments for batfish process",
            "batfish_args");

      addOption(ARG_CLIENT_ARGS, "arguments for the client process",
            "client_args");

      addOption(ARG_COMMAND_FILE, "which command file to use", "command_file");

      addOption(ARG_COORDINATOR_ARGS, "arguments for coordinator process",
            "coordinator_args");

      addBooleanOption(ARG_RUN_CLIENT, "whether to run the client");

      addOption(ARG_RUN_MODE, "which mode to run in (batch|interactive)",
            "run_mode");

      addOption(ARG_TESTRIG_DIR, "where the testrig sits", "testrig_dir");

      addOption(
            BfConsts.ARG_PLUGIN_DIRS,
            "plugin directories to be passed to batfish and client processes",
            "paths");

      addBooleanOption(
            ARG_VERSION,
            "print the version number of the code and exit");
   }

   private void parseCommandLine(String[] args) {
      initCommandLine(args);

      if (getBooleanOptionValue(ARG_HELP)) {
         printHelp(EXECUTABLE_NAME);
         System.exit(0);
      }

      if (getBooleanOptionValue(ARG_VERSION)) {
         System.out.printf("Batfish version: %s\n", Version.getVersion());
         System.exit(0);
      }

      _commandFile = getStringOptionValue(ARG_COMMAND_FILE);
      _logFile = getStringOptionValue(ARG_LOG_FILE);
      _logLevel = getStringOptionValue(ARG_LOG_LEVEL);
      _batfishArgs = getStringOptionValue(ARG_BATFISH_ARGS);
      _clientArgs = getStringOptionValue(ARG_CLIENT_ARGS);
      _coordinatorArgs = getStringOptionValue(ARG_COORDINATOR_ARGS);
      _runClient = getBooleanOptionValue(ARG_RUN_CLIENT);
      _runMode = getStringOptionValue(ARG_RUN_MODE);
      _testrigDir = getStringOptionValue(ARG_TESTRIG_DIR);
      _pluginDirs = getPathListOptionValue(BfConsts.ARG_PLUGIN_DIRS);
   }
}
