package org.batfish.datamodel.answers;

import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.batfish.datamodel.BgpAdvertisement;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.PrefixSpace;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonIdentityReference;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonInclude.Include;
import com.fasterxml.jackson.annotation.JsonProperty;

@JsonInclude(Include.NON_NULL)
public class BgpAdvertisementsAnswerElement implements AnswerElement {

   private static final String ALL_REQUESTED_ADVERTISEMENTS_VAR = "allRequestedAdvertisements";
   private static final String RECEIVED_EBGP_ADVERTISEMENTS_VAR = "receivedEbgpAdvertisements";
   private static final String RECEIVED_IBGP_ADVERTISEMENTS_VAR = "receivedIbgpAdvertisements";
   private static final String SENT_EBGP_ADVERTISEMENTS_VAR = "sentEbgpAdvertisements";
   private static final String SENT_IBGP_ADVERTISEMENTS_VAR = "sentIbgpAdvertisements";

   private final Set<BgpAdvertisement> _allRequestedAdvertisements;

   private final Map<String, Set<BgpAdvertisement>> _receivedEbgpAdvertisements;

   private final Map<String, Set<BgpAdvertisement>> _receivedIbgpAdvertisements;

   private final Map<String, Set<BgpAdvertisement>> _sentEbgpAdvertisements;

   private final Map<String, Set<BgpAdvertisement>> _sentIbgpAdvertisements;

   public BgpAdvertisementsAnswerElement(
         Map<String, Configuration> configurations, Pattern nodeRegex,
         boolean ebgp, boolean ibgp, PrefixSpace prefixSpace, boolean received,
         boolean sent) {
      _allRequestedAdvertisements = new TreeSet<BgpAdvertisement>();
      _receivedEbgpAdvertisements = (received && ebgp) ? new TreeMap<String, Set<BgpAdvertisement>>()
            : null;
      _sentEbgpAdvertisements = (sent && ebgp) ? new TreeMap<String, Set<BgpAdvertisement>>()
            : null;
      _receivedIbgpAdvertisements = (received && ibgp) ? new TreeMap<String, Set<BgpAdvertisement>>()
            : null;
      _sentIbgpAdvertisements = (sent && ibgp) ? new TreeMap<String, Set<BgpAdvertisement>>()
            : null;
      for (Entry<String, Configuration> e : configurations.entrySet()) {
         String hostname = e.getKey();
         Matcher nodeMatcher = nodeRegex.matcher(hostname);
         if (!nodeMatcher.matches()) {
            continue;
         }
         Configuration configuration = e.getValue();
         if (received) {
            if (ebgp) {
               Set<BgpAdvertisement> advertisements = configuration
                     .getReceivedEbgpAdvertisements();
               fill(_receivedEbgpAdvertisements, hostname, advertisements,
                     prefixSpace);
            }
            if (ibgp) {
               Set<BgpAdvertisement> advertisements = configuration
                     .getReceivedIbgpAdvertisements();
               fill(_receivedIbgpAdvertisements, hostname, advertisements,
                     prefixSpace);
            }
         }
         if (sent) {
            if (ebgp) {
               Set<BgpAdvertisement> advertisements = configuration
                     .getSentEbgpAdvertisements();
               fill(_sentEbgpAdvertisements, hostname, advertisements,
                     prefixSpace);
            }
            if (ibgp) {
               Set<BgpAdvertisement> advertisements = configuration
                     .getSentIbgpAdvertisements();
               fill(_sentIbgpAdvertisements, hostname, advertisements,
                     prefixSpace);
            }
         }
      }
   }

   @JsonCreator
   public BgpAdvertisementsAnswerElement(
         @JsonProperty(ALL_REQUESTED_ADVERTISEMENTS_VAR) Set<BgpAdvertisement> allRequested,
         @JsonProperty(RECEIVED_EBGP_ADVERTISEMENTS_VAR) Map<String, Set<BgpAdvertisement>> receivedEbgp,
         @JsonProperty(RECEIVED_IBGP_ADVERTISEMENTS_VAR) Map<String, Set<BgpAdvertisement>> receivedIbgp,
         @JsonProperty(SENT_EBGP_ADVERTISEMENTS_VAR) Map<String, Set<BgpAdvertisement>> sentEbgp,
         @JsonProperty(SENT_IBGP_ADVERTISEMENTS_VAR) Map<String, Set<BgpAdvertisement>> sentIbgp) {

      _allRequestedAdvertisements = allRequested;
      _receivedEbgpAdvertisements = receivedEbgp;
      _receivedIbgpAdvertisements = receivedIbgp;
      _sentEbgpAdvertisements = sentEbgp;
      _sentIbgpAdvertisements = sentIbgp;
   }

   private void fill(Map<String, Set<BgpAdvertisement>> map, String hostname,
         Set<BgpAdvertisement> advertisements, PrefixSpace prefixSpace) {
      Set<BgpAdvertisement> placedAdvertisements = new TreeSet<BgpAdvertisement>();
      map.put(hostname, placedAdvertisements);
      for (BgpAdvertisement advertisement : advertisements) {
         if (prefixSpace.isEmpty()
               || prefixSpace.containsPrefix(advertisement.getNetwork())) {
            placedAdvertisements.add(advertisement);
            _allRequestedAdvertisements.add(advertisement);
         }
      }
   }

   @JsonProperty(ALL_REQUESTED_ADVERTISEMENTS_VAR)
   public Set<BgpAdvertisement> getAllRequestedAdvertisements() {
      return _allRequestedAdvertisements;
   }

   @JsonIdentityReference(alwaysAsId = true)
   @JsonProperty(RECEIVED_EBGP_ADVERTISEMENTS_VAR)
   public Map<String, Set<BgpAdvertisement>> getReceivedEbgpAdvertisements() {
      return _receivedEbgpAdvertisements;
   }

   @JsonIdentityReference(alwaysAsId = true)
   @JsonProperty(RECEIVED_IBGP_ADVERTISEMENTS_VAR)
   public Map<String, Set<BgpAdvertisement>> getReceivedIbgpAdvertisements() {
      return _receivedIbgpAdvertisements;
   }

   @JsonIdentityReference(alwaysAsId = true)
   @JsonProperty(SENT_EBGP_ADVERTISEMENTS_VAR)
   public Map<String, Set<BgpAdvertisement>> getSentEbgpAdvertisements() {
      return _sentEbgpAdvertisements;
   }

   @JsonIdentityReference(alwaysAsId = true)
   @JsonProperty(SENT_IBGP_ADVERTISEMENTS_VAR)
   public Map<String, Set<BgpAdvertisement>> getSentIbgpAdvertisements() {
      return _sentIbgpAdvertisements;
   }

}