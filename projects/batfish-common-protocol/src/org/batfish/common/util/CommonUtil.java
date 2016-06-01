package org.batfish.common.util;

import java.io.File;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.security.cert.CertificateException;
import java.security.cert.X509Certificate;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

import javax.net.ssl.HostnameVerifier;
import javax.net.ssl.SSLContext;
import javax.net.ssl.SSLSession;
import javax.net.ssl.TrustManager;
import javax.net.ssl.X509TrustManager;
import javax.ws.rs.client.ClientBuilder;

import org.apache.commons.io.FileUtils;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;

public class CommonUtil {
   private static class TrustAllHostNameVerifier implements HostnameVerifier {
      @Override
      public boolean verify(String hostname, SSLSession session) {
         return true;
      }
   }

   public static final String FACT_BLOCK_FOOTER = "\n//FACTS END HERE\n"
         + "   }) // clauses\n" + "} <-- .\n";

   public static final String NULL_INTERFACE_NAME = "null_interface";

   public static String applyPrefix(String prefix, String msg) {
      String[] lines = msg.split("\n");
      StringBuilder sb = new StringBuilder();
      for (String line : lines) {
         sb.append(prefix + line + "\n");
      }
      return sb.toString();
   }

   public static long communityStringToLong(String str) {
      String[] parts = str.split(":");
      long high = Long.parseLong(parts[0]);
      long low = Long.parseLong(parts[1]);
      long result = low + (high << 16);
      return result;
   }

   public static String escape(String offendingTokenText) {
      return offendingTokenText.replace("\n", "\\n").replace("\t", "\\t")
            .replace("\r", "\\r");
   }

   public static String extractBits(long l, int start, int end) {
      String s = "";
      for (int pos = end; pos >= start; pos--) {
         long mask = 1L << pos;
         long bit = l & mask;
         s += (bit != 0) ? 1 : 0;
      }
      return s;
   }

   public static ClientBuilder getClientBuilder(boolean secure, boolean trustAll)
         throws Exception {
      if (secure) {
         if (trustAll) {
            SSLContext sslcontext = SSLContext.getInstance("TLS");
            sslcontext.init(null, new TrustManager[] { new X509TrustManager() {
               @Override
               public void checkClientTrusted(X509Certificate[] arg0,
                     String arg1) throws CertificateException {
               }

               @Override
               public void checkServerTrusted(X509Certificate[] arg0,
                     String arg1) throws CertificateException {
               }

               @Override
               public X509Certificate[] getAcceptedIssuers() {
                  return new X509Certificate[0];
               }

            } }, new java.security.SecureRandom());

            return ClientBuilder.newBuilder().sslContext(sslcontext)
                  .hostnameVerifier(new TrustAllHostNameVerifier());
         }
         else {
            return ClientBuilder.newBuilder();
         }
      }
      else {
         return ClientBuilder.newBuilder();
      }
   }

   public static File getConfigProperties(Class<?> locatorClass,
         String propertiesFilename) {
      File configDir = getJarOrClassDir(locatorClass);
      return Paths.get(configDir.toString(), propertiesFilename).toFile();
   }

   public static String getIndentedString(String str, int indentLevel) {
      String indent = getIndentString(indentLevel);
      StringBuilder sb = new StringBuilder();
      String[] lines = str.split("\n");
      for (String line : lines) {
         sb.append(indent + line + "\n");
      }
      return sb.toString();
   }

   public static String getIndentString(int indentLevel) {

      String retString = "";

      for (int i = 0; i < indentLevel; i++) {
         retString += "  ";
      }

      return retString;
   }

   public static Integer getInterfaceVlanNumber(String ifaceName) {
      String prefix = "vlan";
      String ifaceNameLower = ifaceName.toLowerCase();
      String withoutDot = ifaceNameLower.replaceAll("\\.", "");
      if (withoutDot.startsWith(prefix)) {
         String vlanStr = withoutDot.substring(prefix.length());
         if (vlanStr.length() > 0) {
            return Integer.parseInt(vlanStr);
         }
      }
      return null;
   }

   public static File getJarOrClassDir(Class<?> locatorClass) {
      File locatorDirFile = null;
      URL locatorSourceURL = locatorClass.getProtectionDomain().getCodeSource()
            .getLocation();
      String locatorSourceString = locatorSourceURL.toString();
      if (locatorSourceString.startsWith("onejar:")) {
         URL onejarSourceURL = null;
         try {
            onejarSourceURL = Class.forName("com.simontuffs.onejar.Boot")
                  .getProtectionDomain().getCodeSource().getLocation();
         }
         catch (ClassNotFoundException e) {
            throw new BatfishException("could not find onejar class");
         }
         File jarDir = new File(onejarSourceURL.toString().replaceAll(
               "^file:\\\\*", "")).getParentFile();
         return jarDir;
      }
      else {
         char separator = System.getProperty("file.separator").charAt(0);
         String locatorPackageResourceName = locatorClass.getPackage()
               .getName().replace('.', separator);
         try {
            locatorDirFile = new File(locatorClass.getClassLoader()
                  .getResource(locatorPackageResourceName).toURI());
         }
         catch (URISyntaxException e) {
            throw new BatfishException("Failed to resolve locator directory", e);
         }
         assert Boolean.TRUE;
         return locatorDirFile;
      }
   }

   public static List<String> getMatchingStrings(String regex,
         Set<String> allStrings) {
      List<String> matchingStrings = new ArrayList<String>();
      Pattern pattern;
      try {
         pattern = Pattern.compile(regex);
      }
      catch (PatternSyntaxException e) {
         throw new BatfishException(
               "Supplied regex is not a valid java regex: \"" + regex + "\"", e);
      }
      if (pattern != null) {
         for (String s : allStrings) {
            Matcher matcher = pattern.matcher(s);
            if (matcher.matches()) {
               matchingStrings.add(s);
            }
         }
      }
      else {
         matchingStrings.addAll(allStrings);
      }
      return matchingStrings;
   }

   public static String getTime(long millis) {
      long cs = (millis / 10) % 100;
      long s = (millis / 1000) % 60;
      long m = (millis / (1000 * 60)) % 60;
      long h = (millis / (1000 * 60 * 60)) % 24;
      String time = String.format("%02d:%02d:%02d.%02d", h, m, s, cs);
      return time;
   }

   public static int intWidth(int n) {
      if (n == 0) {
         return 1;
      }
      else {
         return 32 - Integer.numberOfLeadingZeros(n);
      }
   }

   public static boolean isLoopback(String interfaceName) {
      return (interfaceName.startsWith("Loopback") || interfaceName
            .startsWith("lo"));
   }

   public static boolean isNullInterface(String ifaceName) {
      String lcIfaceName = ifaceName.toLowerCase();
      return lcIfaceName.startsWith("null");
   }

   public static boolean isValidWildcard(Ip wildcard) {
      long w = wildcard.asLong();
      long wp = w + 1l;
      int numTrailingZeros = Long.numberOfTrailingZeros(wp);
      long check = 1l << numTrailingZeros;
      return wp == check;
   }

   public static String joinStrings(String delimiter, String[] parts) {
      StringBuilder sb = new StringBuilder();
      for (String part : parts) {
         sb.append(part + delimiter);
      }
      String joined = sb.toString();
      int joinedLength = joined.length();
      String result;
      if (joinedLength > 0) {
         result = joined.substring(0, joinedLength - delimiter.length());
      }
      else {
         result = joined;
      }
      return result;
   }

   public static String longToCommunity(Long l) {
      Long upper = l >> 16;
      Long lower = l & 0xFFFF;
      return upper.toString() + ":" + lower;
   }

   public static String md5Digest(String saltedSecret) {
      MessageDigest digest = null;
      try {
         digest = MessageDigest.getInstance("MD5");
      }
      catch (NoSuchAlgorithmException e) {
         throw new BatfishException("Could not initialize md5 hasher", e);
      }
      byte[] plainTextBytes = null;
      try {
         plainTextBytes = saltedSecret.getBytes("UTF-8");
      }
      catch (UnsupportedEncodingException e) {
         throw new BatfishException("Could not convert salted secret to bytes",
               e);
      }
      byte[] digestBytes = digest.digest(plainTextBytes);
      StringBuffer sb = new StringBuffer();
      for (int i = 0; i < digestBytes.length; i++) {
         int digestByteAsInt = 0xff & digestBytes[i];
         if (digestByteAsInt < 0x10) {
            sb.append('0');
         }
         sb.append(Integer.toHexString(digestByteAsInt));
      }
      String md5 = sb.toString();
      return md5;
   }

   public static String readFile(File file) {
      String text = null;
      try {
         text = FileUtils.readFileToString(file);
      }
      catch (IOException e) {
         throw new BatfishException("Failed to read file: " + file.toString(),
               e);
      }
      return text;
   }

   public static Map<Integer, String> toLineMap(String str) {
      Map<Integer, String> map = new TreeMap<Integer, String>();
      String[] lines = str.split("\n");
      for (int i = 0; i < lines.length; i++) {
         String line = lines[i];
         map.put(i, line);
      }
      return map;
   }

   /**
    * Unescapes a string that contains standard Java escape sequences.
    * <ul>
    * <li><strong>&#92;b &#92;f &#92;n &#92;r &#92;t &#92;" &#92;'</strong> :
    * BS, FF, NL, CR, TAB, double and single quote.</li>
    * <li><strong>&#92;X &#92;XX &#92;XXX</strong> : Octal character
    * specification (0 - 377, 0x00 - 0xFF).</li>
    * <li><strong>&#92;uXXXX</strong> : Hexadecimal based Unicode character.</li>
    * </ul>
    *
    * @param st
    *           A string optionally containing standard java escape sequences.
    * @return The translated string.
    */
   public static String unescapeJavaString(String st) {
      if (st == null) {
         return null;
      }
      StringBuilder sb = new StringBuilder(st.length());
      for (int i = 0; i < st.length(); i++) {
         char ch = st.charAt(i);
         if (ch == '\\') {
            char nextChar = (i == st.length() - 1) ? '\\' : st.charAt(i + 1);
            // Octal escape?
            if (nextChar >= '0' && nextChar <= '7') {
               String code = "" + nextChar;
               i++;
               if ((i < st.length() - 1) && st.charAt(i + 1) >= '0'
                     && st.charAt(i + 1) <= '7') {
                  code += st.charAt(i + 1);
                  i++;
                  if ((i < st.length() - 1) && st.charAt(i + 1) >= '0'
                        && st.charAt(i + 1) <= '7') {
                     code += st.charAt(i + 1);
                     i++;
                  }
               }
               sb.append((char) Integer.parseInt(code, 8));
               continue;
            }
            switch (nextChar) {
            case '\\':
               ch = '\\';
               break;
            case 'b':
               ch = '\b';
               break;
            case 'f':
               ch = '\f';
               break;
            case 'n':
               ch = '\n';
               break;
            case 'r':
               ch = '\r';
               break;
            case 't':
               ch = '\t';
               break;
            case '\"':
               ch = '\"';
               break;
            case '\'':
               ch = '\'';
               break;
            // Hex Unicode: u????
            case 'u':
               if (i >= st.length() - 5) {
                  ch = 'u';
                  break;
               }
               int code = Integer.parseInt(
                     "" + st.charAt(i + 2) + st.charAt(i + 3)
                           + st.charAt(i + 4) + st.charAt(i + 5), 16);
               sb.append(Character.toChars(code));
               i += 5;
               continue;
            }
            i++;
         }
         sb.append(ch);
      }
      return sb.toString();
   }

   public static void writeFile(String outputPath, String output) {
      File outputFile = new File(outputPath);
      try {
         FileUtils.write(outputFile, output);
      }
      catch (IOException e) {
         throw new BatfishException("Failed to write file: " + outputPath, e);
      }
   }
}