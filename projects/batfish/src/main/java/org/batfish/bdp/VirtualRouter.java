package org.batfish.bdp;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.stream.Collectors;
import org.batfish.common.BatfishException;
import org.batfish.common.util.ComparableStructure;
import org.batfish.datamodel.AbstractRoute;
import org.batfish.datamodel.AsPath;
import org.batfish.datamodel.BgpAdvertisement;
import org.batfish.datamodel.BgpAdvertisement.BgpAdvertisementType;
import org.batfish.datamodel.BgpNeighbor;
import org.batfish.datamodel.BgpRoute;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConnectedRoute;
import org.batfish.datamodel.Edge;
import org.batfish.datamodel.GeneratedRoute;
import org.batfish.datamodel.Interface;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.OriginType;
import org.batfish.datamodel.OspfArea;
import org.batfish.datamodel.OspfExternalRoute;
import org.batfish.datamodel.OspfExternalType1Route;
import org.batfish.datamodel.OspfExternalType2Route;
import org.batfish.datamodel.OspfInterAreaRoute;
import org.batfish.datamodel.OspfIntraAreaRoute;
import org.batfish.datamodel.OspfMetricType;
import org.batfish.datamodel.OspfProcess;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.Route;
import org.batfish.datamodel.RouteFilterList;
import org.batfish.datamodel.RoutingProtocol;
import org.batfish.datamodel.StaticRoute;
import org.batfish.datamodel.Topology;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.collections.AdvertisementSet;
import org.batfish.datamodel.collections.EdgeSet;
import org.batfish.datamodel.routing_policy.RoutingPolicy;

public class VirtualRouter extends ComparableStructure<String> {

   /**
    *
    */
   private static final long serialVersionUID = 1L;

   transient BgpMultipathRib _baseEbgpRib;

   transient BgpMultipathRib _baseIbgpRib;

   transient BgpBestPathRib _bgpBestPathRib;

   transient BgpMultipathRib _bgpMultipathRib;

   final Configuration _c;

   transient ConnectedRib _connectedRib;

   transient BgpBestPathRib _ebgpBestPathRib;

   transient BgpMultipathRib _ebgpMultipathRib;

   transient BgpMultipathRib _ebgpStagingRib;

   Fib _fib;

   transient Rib _generatedRib;

   transient BgpBestPathRib _ibgpBestPathRib;

   transient BgpMultipathRib _ibgpMultipathRib;

   transient BgpMultipathRib _ibgpStagingRib;

   transient Rib _independentRib;

   Rib _mainRib;

   private final Map<String, Node> _nodes;

   transient OspfExternalType1Rib _ospfExternalType1Rib;

   transient OspfExternalType1Rib _ospfExternalType1StagingRib;

   transient OspfExternalType2Rib _ospfExternalType2Rib;

   transient OspfExternalType2Rib _ospfExternalType2StagingRib;

   transient OspfInterAreaRib _ospfInterAreaRib;

   transient OspfInterAreaRib _ospfInterAreaStagingRib;

   transient OspfIntraAreaRib _ospfIntraAreaRib;

   transient OspfIntraAreaRib _ospfIntraAreaStagingRib;

   transient OspfRib _ospfRib;

   transient BgpBestPathRib _prevBgpBestPathRib;

   transient BgpMultipathRib _prevBgpRib;

   transient BgpBestPathRib _prevEbgpBestPathRib;

   transient BgpMultipathRib _prevEbgpRib;

   transient BgpBestPathRib _prevIbgpBestPathRib;

   transient BgpMultipathRib _prevIbgpRib;

   transient Rib _prevMainRib;

   transient OspfExternalType1Rib _prevOspfExternalType1Rib;

   transient OspfExternalType2Rib _prevOspfExternalType2Rib;

   AdvertisementSet _receivedBgpAdvertisements;

   AdvertisementSet _sentBgpAdvertisements;

   transient StaticRib _staticInterfaceRib;

   transient StaticRib _staticRib;

   final Vrf _vrf;

   public VirtualRouter(String name, Configuration c, Map<String, Node> nodes) {
      super(name);
      _c = c;
      _nodes = nodes;
      _vrf = c.getVrfs().get(name);
   }

   public boolean activateGeneratedRoutes() {
      boolean changed = false;
      for (GeneratedRoute gr : _vrf.getGeneratedRoutes()) {
         boolean active = true;
         String generationPolicyName = gr.getGenerationPolicy();
         GeneratedRoute.Builder grb = new GeneratedRoute.Builder();
         grb.setNetwork(gr.getNetwork());
         grb.setAdmin(gr.getAdministrativeCost());
         grb.setMetric(gr.getMetric() != null ? gr.getMetric() : 0);
         grb.setAttributePolicy(gr.getAttributePolicy());
         grb.setGenerationPolicy(gr.getGenerationPolicy());
         boolean discard = gr.getDiscard();
         grb.setDiscard(discard);
         if (discard) {
            grb.setNextHopInterface(Interface.NULL_INTERFACE_NAME);
         }
         if (generationPolicyName != null) {
            RoutingPolicy generationPolicy = _c.getRoutingPolicies()
                  .get(generationPolicyName);
            if (generationPolicy != null) {
               active = false;
               for (AbstractRoute contributingRoute : _prevMainRib
                     .getRoutes()) {
                  boolean accept = generationPolicy.process(contributingRoute,
                        grb, null, _key);
                  if (accept) {
                     if (!discard) {
                        grb.setNextHopIp(contributingRoute.getNextHopIp());
                     }
                     active = true;
                     break;
                  }
               }
            }
         }
         if (active) {
            GeneratedRoute newGr = grb.build();
            if (_generatedRib.mergeRoute(newGr)) {
               changed = true;
            }
         }
      }
      return changed;
   }

   public boolean activateStaticRoutes() {
      boolean changed = false;
      for (StaticRoute sr : _staticRib.getRoutes()) {
         Set<AbstractRoute> matchingRoutes = _prevMainRib
               .longestPrefixMatch(sr.getNextHopIp());
         Prefix prefix = sr.getNetwork();
         for (AbstractRoute matchingRoute : matchingRoutes) {
            Prefix matchingRoutePrefix = matchingRoute.getNetwork();
            // check to make sure matching route's prefix does not totally
            // contain this static route's prefix
            if (matchingRoutePrefix.getAddress().asLong() > prefix.getAddress()
                  .asLong()
                  || matchingRoutePrefix.getEndAddress().asLong() < prefix
                  .getEndAddress().asLong()) {
               if (_mainRib.mergeRoute(sr)) {
                  changed = true;
               }
               break;
            }
         }
      }
      return changed;
   }

   public void computeFib() {
      _fib = new Fib(_mainRib);
   }

   public boolean computeInterAreaSummaries() {
      OspfProcess proc = _vrf.getOspfProcess();
      boolean changed = false;
      if (proc != null) {
         int admin = RoutingProtocol.OSPF_IA
               .getSummaryAdministrativeCost(_c.getConfigurationFormat());
         for (Entry<Long, OspfArea> e : proc.getAreas().entrySet()) {
            long areaNum = e.getKey();
            OspfArea area = e.getValue();
            for (Entry<Prefix, Boolean> e2 : area.getSummaries().entrySet()) {
               Prefix prefix = e2.getKey();
               boolean advertise = e2.getValue();
               if (advertise) {
                  Integer metric = null;
                  for (OspfIntraAreaRoute contributingRoute : _ospfIntraAreaRib
                        .getRoutes()) {
                     if (contributingRoute.getArea() != areaNum) {
                        Prefix contributingRoutePrefix = contributingRoute
                              .getNetwork();
                        if (prefix.containsPrefix(contributingRoutePrefix)) {
                           int contributingRouteMetric = contributingRoute
                                 .getMetric();
                           if (metric == null) {
                              metric = contributingRouteMetric;
                           }
                           else {
                              metric = Math.min(
                                    metric,
                                    contributingRouteMetric);
                           }
                        }
                     }
                  }
                  for (OspfInterAreaRoute contributingRoute : _ospfInterAreaRib
                        .getRoutes()) {
                     if (contributingRoute.getArea() != areaNum) {
                        Prefix contributingRoutePrefix = contributingRoute
                              .getNetwork();
                        if (prefix.containsPrefix(contributingRoutePrefix)) {
                           int contributingRouteMetric = contributingRoute
                                 .getMetric();
                           if (metric == null) {
                              metric = contributingRouteMetric;
                           }
                           else {
                              metric = Math.min(
                                    metric,
                                    contributingRouteMetric);
                           }
                        }
                     }
                  }
                  if (metric != null) {
                     OspfInterAreaRoute summaryRoute = new OspfInterAreaRoute(
                           prefix, Ip.ZERO, admin, metric, areaNum);
                     if (_ospfInterAreaStagingRib.mergeRoute(summaryRoute)) {
                        changed = true;
                     }
                  }
               }
            }
         }
      }
      return changed;
   }

   public <U extends AbstractRoute, T extends U> void importRib(
         AbstractRib<U> importingRib, AbstractRib<T> exportingRib) {
      for (T route : exportingRib.getRoutes()) {
         importingRib.mergeRoute(route);
      }
   }

   public void initBaseBgpRibs(
         AdvertisementSet externalAdverts,
         Map<Ip, Set<String>> ipOwners) {
      _bgpMultipathRib = new BgpMultipathRib(this);
      _baseEbgpRib = new BgpMultipathRib(this);
      _baseIbgpRib = new BgpMultipathRib(this);

      if (_vrf.getBgpProcess() != null) {
         int ebgpAdmin = RoutingProtocol.BGP
               .getDefaultAdministrativeCost(_c.getConfigurationFormat());
         int ibgpAdmin = RoutingProtocol.IBGP
               .getDefaultAdministrativeCost(_c.getConfigurationFormat());

         for (BgpAdvertisement advert : externalAdverts) {
            if (advert.getDstNode().equals(_c.getHostname())) {
               Ip dstIp = advert.getDstIp();
               Set<String> dstIpOwners = ipOwners.get(dstIp);
               String hostname = _c.getHostname();
               if (dstIpOwners == null || !dstIpOwners.contains(hostname)) {
                  continue;
               }
               Ip srcIp = advert.getSrcIp();
               // TODO: support passive bgp connections
               Prefix srcPrefix = new Prefix(srcIp, Prefix.MAX_PREFIX_LENGTH);
               BgpNeighbor neighbor = _vrf.getBgpProcess().getNeighbors()
                     .get(srcPrefix);
               if (neighbor != null) {
                  BgpAdvertisementType type = advert.getType();
                  BgpRoute.Builder outgoingRouteBuilder = new BgpRoute.Builder();
                  boolean ebgp;
                  boolean received;
                  switch (type) {

                  case EBGP_RECEIVED:
                     ebgp = true;
                     received = true;
                     break;

                  case EBGP_SENT:
                     ebgp = true;
                     received = false;
                     break;

                  case IBGP_RECEIVED:
                     ebgp = false;
                     received = true;
                     break;

                  case IBGP_SENT:
                     ebgp = false;
                     received = false;
                     break;

                  case EBGP_ORIGINATED:
                  case IBGP_ORIGINATED:
                  default:
                     throw new BatfishException(
                           "Missing or invalid bgp advertisement type");

                  }
                  BgpMultipathRib targetRib = ebgp ? _baseEbgpRib
                        : _baseIbgpRib;
                  RoutingProtocol targetProtocol = ebgp ? RoutingProtocol.BGP
                        : RoutingProtocol.IBGP;

                  if (received) {
                     int admin = ebgp ? ebgpAdmin : ibgpAdmin;
                     AsPath asPath = advert.getAsPath();
                     SortedSet<Long> clusterList = advert.getClusterList();
                     SortedSet<Long> communities = new TreeSet<>(
                           advert.getCommunities());
                     int localPreference = advert.getLocalPreference();
                     int metric = advert.getMed();
                     Prefix network = advert.getNetwork();
                     Ip nextHopIp = advert.getNextHopIp();
                     Ip originatorIp = advert.getOriginatorIp();
                     OriginType originType = advert.getOriginType();
                     RoutingProtocol srcProtocol = advert.getSrcProtocol();
                     int weight = advert.getWeight();
                     BgpRoute.Builder builder = new BgpRoute.Builder();
                     builder.setAdmin(admin);
                     builder.setAsPath(asPath.getAsSets());
                     builder.setClusterList(clusterList);
                     builder.setCommunities(communities);
                     builder.setLocalPreference(localPreference);
                     builder.setMetric(metric);
                     builder.setNetwork(network);
                     builder.setNextHopIp(nextHopIp);
                     builder.setOriginatorIp(originatorIp);
                     builder.setOriginType(originType);
                     builder.setProtocol(targetProtocol);
                     // TODO: support external route reflector clients
                     builder.setReceivedFromRouteReflectorClient(false);
                     builder.setSrcProtocol(srcProtocol);
                     // TODO: possibly suppport setting tag
                     builder.setWeight(weight);
                     BgpRoute route = builder.build();
                     targetRib.mergeRoute(route);
                  }
                  else {
                     int localPreference;
                     if (ebgp) {
                        localPreference = BgpRoute.DEFAULT_LOCAL_PREFERENCE;
                     }
                     else {
                        localPreference = advert.getLocalPreference();
                     }
                     outgoingRouteBuilder
                           .setAsPath(advert.getAsPath().getAsSets());
                     outgoingRouteBuilder.setCommunities(
                           new TreeSet<>(advert.getCommunities()));
                     outgoingRouteBuilder.setLocalPreference(localPreference);
                     outgoingRouteBuilder.setMetric(advert.getMed());
                     outgoingRouteBuilder.setNetwork(advert.getNetwork());
                     outgoingRouteBuilder.setNextHopIp(advert.getNextHopIp());
                     outgoingRouteBuilder
                           .setOriginatorIp(advert.getOriginatorIp());
                     outgoingRouteBuilder.setOriginType(advert.getOriginType());
                     outgoingRouteBuilder.setProtocol(targetProtocol);
                     // TODO:
                     // outgoingRouteBuilder.setReceivedFromRouteReflectorClient(...);
                     outgoingRouteBuilder
                           .setSrcProtocol(advert.getSrcProtocol());
                     BgpRoute transformedOutgoingRoute = outgoingRouteBuilder
                           .build();
                     BgpRoute.Builder transformedIncomingRouteBuilder = new BgpRoute.Builder();

                     // Incoming originatorIp
                     transformedIncomingRouteBuilder.setOriginatorIp(
                           transformedOutgoingRoute.getOriginatorIp());

                     // Incoming clusterList
                     transformedIncomingRouteBuilder.getClusterList()
                           .addAll(transformedOutgoingRoute.getClusterList());

                     // Incoming receivedFromRouteReflectorClient
                     transformedIncomingRouteBuilder
                           .setReceivedFromRouteReflectorClient(
                                 transformedOutgoingRoute
                                       .getReceivedFromRouteReflectorClient());

                     // Incoming asPath
                     transformedIncomingRouteBuilder.setAsPath(
                           transformedOutgoingRoute.getAsPath().getAsSets());

                     // Incoming communities
                     transformedIncomingRouteBuilder.getCommunities()
                           .addAll(transformedOutgoingRoute.getCommunities());

                     // Incoming protocol
                     transformedIncomingRouteBuilder
                           .setProtocol(targetProtocol);

                     // Incoming network
                     transformedIncomingRouteBuilder
                           .setNetwork(transformedOutgoingRoute.getNetwork());

                     // Incoming nextHopIp
                     transformedIncomingRouteBuilder.setNextHopIp(
                           transformedOutgoingRoute.getNextHopIp());

                     // Incoming originType
                     transformedIncomingRouteBuilder.setOriginType(
                           transformedOutgoingRoute.getOriginType());

                     // Incoming localPreference
                     transformedIncomingRouteBuilder.setLocalPreference(
                           transformedOutgoingRoute.getLocalPreference());

                     // Incoming admin
                     int admin = ebgp ? ebgpAdmin : ibgpAdmin;
                     transformedIncomingRouteBuilder.setAdmin(admin);

                     // Incoming metric
                     transformedIncomingRouteBuilder
                           .setMetric(transformedOutgoingRoute.getMetric());

                     // Incoming srcProtocol
                     transformedIncomingRouteBuilder
                           .setSrcProtocol(targetProtocol);
                     String importPolicyName = neighbor.getImportPolicy();
                     // TODO: ensure there is always an import policy

                     if (ebgp
                           && transformedOutgoingRoute.getAsPath()
                           .containsAs(neighbor.getLocalAs())
                           && !neighbor.getAllowLocalAsIn()) {
                        // skip routes containing peer's AS unless
                        // disable-peer-as-check (getAllowRemoteAsOut) is set
                        continue;
                     }

                     /*
                      * CREATE INCOMING ROUTE
                      */
                     boolean acceptIncoming = true;
                     if (importPolicyName != null) {
                        RoutingPolicy importPolicy = _c.getRoutingPolicies()
                              .get(importPolicyName);
                        if (importPolicy != null) {
                           acceptIncoming = importPolicy.process(
                                 transformedOutgoingRoute,
                                 transformedIncomingRouteBuilder,
                                 advert.getSrcIp(), _key);
                        }
                     }
                     if (acceptIncoming) {
                        BgpRoute transformedIncomingRoute = transformedIncomingRouteBuilder
                              .build();
                        targetRib.mergeRoute(transformedIncomingRoute);
                     }
                  }
               }
            }
         }
      }

      _ebgpMultipathRib = new BgpMultipathRib(this);
      _ibgpMultipathRib = new BgpMultipathRib(this);
      _ebgpBestPathRib = new BgpBestPathRib(this);
      _ibgpBestPathRib = new BgpBestPathRib(this);
      _bgpBestPathRib = new BgpBestPathRib(this);
      importRib(_ebgpMultipathRib, _baseEbgpRib);
      importRib(_ebgpBestPathRib, _baseEbgpRib);
      importRib(_bgpBestPathRib, _baseEbgpRib);
      importRib(_ibgpMultipathRib, _baseIbgpRib);
      importRib(_ibgpBestPathRib, _baseIbgpRib);
      importRib(_bgpBestPathRib, _baseIbgpRib);
   }

   public void initBaseOspfRoutes() {
      if (_vrf.getOspfProcess() != null) {
         // init intra-area routes from connected routes
         _vrf.getOspfProcess().getAreas().forEach((areaNum, area) -> {
            for (Interface iface : area.getInterfaces()) {
               if (iface.getActive()) {
                  Set<Prefix> allNetworkPrefixes = iface.getAllPrefixes()
                        .stream().map(prefix -> prefix.getNetworkPrefix())
                        .collect(Collectors.toSet());
                  int cost = iface.getOspfCost();
                  for (Prefix prefix : allNetworkPrefixes) {
                     OspfIntraAreaRoute route = new OspfIntraAreaRoute(prefix,
                           null,
                           RoutingProtocol.OSPF.getDefaultAdministrativeCost(
                                 _c.getConfigurationFormat()),
                           cost, areaNum);
                     _ospfIntraAreaRib.mergeRoute(route);
                  }
               }
            }
         });
      }
   }

   /**
    * This function creates BGP routes from generated routes that go into the
    * BGP RIB, but cannot be imported into the main RIB. The purpose of these
    * routes is to prevent the local router from accepting advertisements less
    * desirable than the local generated ones for the given network. They are
    * not themselves advertised.
    */
   public void initBgpAggregateRoutes() {
      // first import aggregates
      switch (_c.getConfigurationFormat()) {
      case JUNIPER:
      case JUNIPER_SWITCH:
         return;
      // $CASES-OMITTED$
      default:
         break;
      }
      for (AbstractRoute grAbstract : _generatedRib.getRoutes()) {
         GeneratedRoute gr = (GeneratedRoute) grAbstract;
         BgpRoute.Builder b = new BgpRoute.Builder();
         b.setAdmin(gr.getAdministrativeCost());
         b.setAsPath(gr.getAsPath().getAsSets());
         b.setMetric(gr.getMetric());
         b.setSrcProtocol(RoutingProtocol.AGGREGATE);
         b.setProtocol(RoutingProtocol.AGGREGATE);
         b.setNetwork(gr.getNetwork());
         b.setLocalPreference(BgpRoute.DEFAULT_LOCAL_PREFERENCE);
         /**
          * Note: Origin type and originator IP should get overwritten, but are
          * needed initially
          */
         b.setOriginatorIp(_vrf.getBgpProcess().getRouterId());
         b.setOriginType(OriginType.INCOMPLETE);
         BgpRoute br = b.build();
         br.setNonRouting(true);
         _bgpMultipathRib.mergeRoute(br);
         _bgpBestPathRib.mergeRoute(br);
      }

   }

   public void initConnectedRib() {
      for (Interface i : _vrf.getInterfaces().values()) {
         if (i.getActive()) {
            for (Prefix ifacePrefix : i.getAllPrefixes()) {
               Prefix prefix = ifacePrefix.getNetworkPrefix();
               ConnectedRoute cr = new ConnectedRoute(prefix, i.getName());
               _connectedRib.mergeRoute(cr);
            }
         }
      }
   }

   public void initEbgpTopology(BdpDataPlane dp) {
      if (_vrf.getBgpProcess() != null) {
         String hostname = _c.getHostname();
         for (BgpNeighbor neighbor : _vrf.getBgpProcess().getNeighbors()
               .values()) {
            boolean ebgpSession = !neighbor.getRemoteAs()
                  .equals(neighbor.getLocalAs());
            if (ebgpSession) {
               BgpNeighbor remoteNeighbor = neighbor.getRemoteBgpNeighbor();
               if (remoteNeighbor != null) {
                  Set<String> localIpOwners = dp.getIpOwners()
                        .get(neighbor.getLocalIp());
                  boolean nodeOwnsLocalIp = localIpOwners.contains(hostname);
                  Set<String> remoteLocalIpOwners = dp.getIpOwners()
                        .get(remoteNeighbor.getLocalIp());
                  String remoteHostname = remoteNeighbor.getOwner()
                        .getHostname();
                  boolean remoteNeighborOwnsRemoteLocalIp = remoteLocalIpOwners
                        .contains(remoteHostname);
                  if (nodeOwnsLocalIp && remoteNeighborOwnsRemoteLocalIp) {
                     // pretty confident we have a bgp connection here
                     // for now, just leave it alone
                  }
                  else {
                     neighbor.setRemoteBgpNeighbor(null);
                     remoteNeighbor.setRemoteBgpNeighbor(null);
                  }
               }
            }
         }
      }
   }

   public void initIbgpTopology(BdpDataPlane dp) {
      // TODO: implement
   }

   public void initOspfExports() {
      if (_vrf.getOspfProcess() != null) {
         // init ospf exports
         String exportPolicyName = _vrf.getOspfProcess().getExportPolicy();
         if (exportPolicyName != null) {
            RoutingPolicy exportPolicy = _c.getRoutingPolicies()
                  .get(exportPolicyName);
            if (exportPolicy != null) {
               for (AbstractRoute potentialExport : _prevMainRib.getRoutes()) {
                  OspfExternalRoute.Builder outputRouteBuilder = new OspfExternalRoute.Builder();
                  boolean accept = exportPolicy.process(potentialExport,
                        outputRouteBuilder, null, _key);
                  if (accept) {
                     outputRouteBuilder.setAdmin(outputRouteBuilder
                           .getOspfMetricType().toRoutingProtocol()
                           .getDefaultAdministrativeCost(
                                 _c.getConfigurationFormat()));
                     outputRouteBuilder
                           .setNetwork(potentialExport.getNetwork());
                     outputRouteBuilder.setCostToAdvertiser(0);
                     outputRouteBuilder.setAdvertiser(_c.getHostname());
                     OspfExternalRoute outputRoute = outputRouteBuilder.build();
                     outputRoute.setNonRouting(true);
                     // shouldn't be null
                     if (outputRoute.getOspfMetricType() == OspfMetricType.E1) {
                        _ospfExternalType1Rib
                              .mergeRoute((OspfExternalType1Route) outputRoute);
                     }
                     else {
                        _ospfExternalType2Rib
                              .mergeRoute((OspfExternalType2Route) outputRoute);
                     }
                  }
               }
            }
         }
      }
   }

   public void initRibs() {
      _bgpMultipathRib = new BgpMultipathRib(this);
      _connectedRib = new ConnectedRib(this);
      _ebgpMultipathRib = new BgpMultipathRib(this);
      _ebgpStagingRib = new BgpMultipathRib(this);
      _ibgpMultipathRib = new BgpMultipathRib(this);
      _ibgpStagingRib = new BgpMultipathRib(this);
      _independentRib = new Rib(this);
      _mainRib = new Rib(this);
      _ospfExternalType1Rib = new OspfExternalType1Rib(this);
      _ospfExternalType2Rib = new OspfExternalType2Rib(this);
      _ospfExternalType1StagingRib = new OspfExternalType1Rib(this);
      _ospfExternalType2StagingRib = new OspfExternalType2Rib(this);
      _ospfInterAreaRib = new OspfInterAreaRib(this);
      _ospfInterAreaStagingRib = new OspfInterAreaRib(this);
      _ospfIntraAreaRib = new OspfIntraAreaRib(this);
      _ospfIntraAreaStagingRib = new OspfIntraAreaRib(this);
      _ospfRib = new OspfRib(this);
      _staticRib = new StaticRib(this);
      _staticInterfaceRib = new StaticRib(this);
   }

   public void initStaticRib() {
      for (StaticRoute sr : _vrf.getStaticRoutes()) {
         String nextHopInt = sr.getNextHopInterface();
         if (nextHopInt != null
               && !Interface.NULL_INTERFACE_NAME.equals(nextHopInt)
               && !_vrf.getInterfaces().get(nextHopInt).getActive()) {
            continue;
         }
         // interface route
         if (sr.getNextHopIp().equals(Route.UNSET_ROUTE_NEXT_HOP_IP)) {
            _staticInterfaceRib.mergeRoute(sr);
         }
         else {
            _staticRib.mergeRoute(sr);
         }
      }
   }

   public int propagateBgpRoutes(
         Map<String, Node> nodes,
         Map<Ip, Set<String>> ipOwners) {
      int numRoutes = 0;
      _receivedBgpAdvertisements = new AdvertisementSet();
      _sentBgpAdvertisements = new AdvertisementSet();
      if (_vrf.getBgpProcess() != null) {
         int ebgpAdmin = RoutingProtocol.BGP
               .getDefaultAdministrativeCost(_c.getConfigurationFormat());
         int ibgpAdmin = RoutingProtocol.IBGP
               .getDefaultAdministrativeCost(_c.getConfigurationFormat());

         for (BgpNeighbor neighbor : _vrf.getBgpProcess().getNeighbors()
               .values()) {
            Ip localIp = neighbor.getLocalIp();
            Set<String> localIpOwners = ipOwners.get(localIp);
            String hostname = _c.getHostname();
            if (localIpOwners == null || !localIpOwners.contains(hostname)) {
               continue;
            }
            BgpNeighbor remoteBgpNeighbor = neighbor.getRemoteBgpNeighbor();
            if (remoteBgpNeighbor != null) {
               int localAs = neighbor.getLocalAs();
               int remoteAs = neighbor.getRemoteAs();
               Configuration remoteConfig = remoteBgpNeighbor.getOwner();
               String remoteHostname = remoteConfig.getHostname();
               String remoteVrfName = remoteBgpNeighbor.getVrf();
               Vrf remoteVrf = remoteConfig.getVrfs().get(remoteVrfName);
               VirtualRouter remoteVirtualRouter = _nodes
                     .get(remoteHostname)._virtualRouters.get(remoteVrfName);
               RoutingPolicy remoteExportPolicy = remoteConfig
                     .getRoutingPolicies()
                     .get(remoteBgpNeighbor.getExportPolicy());
               boolean ebgpSession = localAs != remoteAs;
               BgpMultipathRib targetRib = ebgpSession ? _ebgpStagingRib
                     : _ibgpStagingRib;
               RoutingProtocol targetProtocol = ebgpSession
                     ? RoutingProtocol.BGP : RoutingProtocol.IBGP;
               Set<AbstractRoute> remoteCandidateRoutes = Collections
                     .newSetFromMap(new IdentityHashMap<>());

               /**
                * Add IGP routes.
                */
               Set<AbstractRoute> activeRemoteRoutes = Collections
                     .newSetFromMap(new IdentityHashMap<>());
               activeRemoteRoutes
                     .addAll(remoteVirtualRouter._prevMainRib.getRoutes());
               for (AbstractRoute remoteCandidateRoute : activeRemoteRoutes) {
                  if (remoteCandidateRoute.getProtocol() != RoutingProtocol.BGP
                        && remoteCandidateRoute
                        .getProtocol() != RoutingProtocol.IBGP) {
                     remoteCandidateRoutes.add(remoteCandidateRoute);
                  }
               }

               /*
                * bgp advertise-external
                *
                * When this is set, add best eBGP path independently of whether
                * it is preempted by an iBGP or IGP route. Only applicable to
                * iBGP sessions.
                */
               boolean advertiseExternal = !ebgpSession
                     && remoteBgpNeighbor.getAdvertiseExternal();
               if (advertiseExternal) {
                  remoteCandidateRoutes.addAll(
                        remoteVirtualRouter._prevEbgpBestPathRib.getRoutes());
               }

               /*
                * bgp advertise-inactive
                *
                * When this is set, add best BGP path independently of whether
                * it is preempted by an IGP route. Only applicable to eBGP
                * sessions.
                */
               boolean advertiseInactive = ebgpSession
                     && remoteBgpNeighbor.getAdvertiseInactive();
               /**
                * Add best bgp paths if they are active, or if
                * advertise-inactive
                */
               for (AbstractRoute remoteCandidateRoute : remoteVirtualRouter._prevBgpBestPathRib
                     .getRoutes()) {
                  if (advertiseInactive
                        || activeRemoteRoutes.contains(remoteCandidateRoute)) {
                     remoteCandidateRoutes.add(remoteCandidateRoute);
                  }
               }

               /**
                * Add all bgp paths if additional-paths active for this session
                */
               boolean additionalPaths = !ebgpSession
                     && neighbor.getAdditionalPathsReceive()
                     && remoteBgpNeighbor.getAdditionalPathsSend()
                     && remoteBgpNeighbor.getAdditionalPathsSelectAll();
               if (additionalPaths) {
                  for (AbstractRoute remoteCandidateRoute : remoteVirtualRouter._prevBgpRib
                        .getRoutes()) {
                     remoteCandidateRoutes.add(remoteCandidateRoute);
                  }
               }
               for (AbstractRoute remoteRoute : remoteCandidateRoutes) {
                  BgpRoute.Builder transformedOutgoingRouteBuilder = new BgpRoute.Builder();
                  RoutingProtocol remoteRouteProtocol = remoteRoute
                        .getProtocol();
                  boolean remoteRouteIsBgp = remoteRouteProtocol == RoutingProtocol.IBGP
                        || remoteRouteProtocol == RoutingProtocol.BGP;

                  // originatorIP
                  Ip originatorIp;
                  if (!ebgpSession
                        && remoteRouteProtocol.equals(RoutingProtocol.IBGP)) {
                     BgpRoute bgpRemoteRoute = (BgpRoute) remoteRoute;
                     originatorIp = bgpRemoteRoute.getOriginatorIp();
                  }
                  else {
                     originatorIp = remoteVrf.getBgpProcess().getRouterId();
                  }
                  transformedOutgoingRouteBuilder.setOriginatorIp(originatorIp);

                  // clusterList, receivedFromRouteReflectorClient, (originType
                  // for bgp remote route)
                  if (remoteRouteIsBgp) {
                     BgpRoute bgpRemoteRoute = (BgpRoute) remoteRoute;
                     transformedOutgoingRouteBuilder
                           .setOriginType(bgpRemoteRoute.getOriginType());
                     if (ebgpSession
                           && bgpRemoteRoute.getAsPath()
                           .containsAs(remoteBgpNeighbor.getRemoteAs())
                           && !remoteBgpNeighbor.getAllowRemoteAsOut()) {
                        // skip routes containing peer's AS unless
                        // disable-peer-as-check (getAllowRemoteAsOut) is set
                        continue;
                     }
                     /*
                      * route reflection: reflect everything received from
                      * clients to clients and non-clients. reflect everything
                      * received from non-clients to clients. Do not reflect to
                      * originator
                      */

                     Ip remoteOriginatorIp = bgpRemoteRoute.getOriginatorIp();
                     // don't accept routes whose originator ip is my BGP id
                     if (remoteOriginatorIp != null && _vrf.getBgpProcess()
                           .getRouterId().equals(remoteOriginatorIp)) {
                        continue;
                     }
                     if (remoteRouteProtocol.equals(RoutingProtocol.IBGP)
                           && !ebgpSession) {
                        boolean remoteRouteReceivedFromRouteReflectorClient = bgpRemoteRoute
                              .getReceivedFromRouteReflectorClient();
                        boolean sendingToRouteReflectorClient = remoteBgpNeighbor
                              .getRouteReflectorClient();
                        boolean newRouteReceivedFromRouteReflectorClient = neighbor
                              .getRouteReflectorClient();
                        transformedOutgoingRouteBuilder
                              .setReceivedFromRouteReflectorClient(
                                    newRouteReceivedFromRouteReflectorClient);
                        transformedOutgoingRouteBuilder.getClusterList()
                              .addAll(bgpRemoteRoute.getClusterList());
                        if (!remoteRouteReceivedFromRouteReflectorClient
                              && !sendingToRouteReflectorClient) {
                           continue;
                        }
                        if (sendingToRouteReflectorClient) {
                           // sender adds its local cluster id to clusterlist of
                           // new route
                           transformedOutgoingRouteBuilder.getClusterList()
                                 .add(remoteBgpNeighbor.getClusterId());
                        }
                        if (transformedOutgoingRouteBuilder.getClusterList()
                              .contains(neighbor.getClusterId())) {
                           // receiver will reject new route if it contains its
                           // local cluster id
                           continue;
                        }
                     }
                  }

                  // Outgoing asPath
                  // Outgoing communities
                  if (remoteRouteIsBgp) {
                     BgpRoute bgpRemoteRoute = (BgpRoute) remoteRoute;
                     transformedOutgoingRouteBuilder
                           .setAsPath(bgpRemoteRoute.getAsPath().getAsSets());
                     if (remoteBgpNeighbor.getSendCommunity()) {
                        transformedOutgoingRouteBuilder.getCommunities()
                              .addAll(bgpRemoteRoute.getCommunities());
                     }
                  }
                  if (ebgpSession) {
                     SortedSet<Integer> newAsPathElement = new TreeSet<>();
                     newAsPathElement.add(remoteAs);
                     transformedOutgoingRouteBuilder.getAsPath().add(
                           0,
                           newAsPathElement);
                  }

                  // Outgoing protocol
                  transformedOutgoingRouteBuilder.setProtocol(targetProtocol);
                  transformedOutgoingRouteBuilder
                        .setNetwork(remoteRoute.getNetwork());

                  // Outgoing metric
                  if (remoteRouteIsBgp) {
                     transformedOutgoingRouteBuilder
                           .setMetric(remoteRoute.getMetric());
                  }

                  // Outgoing nextHopIp
                  // Outgoing localPreference
                  Ip nextHopIp;
                  int localPreference;
                  if (ebgpSession || !remoteRouteIsBgp) {
                     nextHopIp = remoteBgpNeighbor.getLocalIp();
                     localPreference = BgpRoute.DEFAULT_LOCAL_PREFERENCE;
                  }
                  else {
                     nextHopIp = remoteRoute.getNextHopIp();
                     BgpRoute remoteIbgpRoute = (BgpRoute) remoteRoute;
                     localPreference = remoteIbgpRoute.getLocalPreference();
                  }
                  if (nextHopIp.equals(Route.UNSET_ROUTE_NEXT_HOP_IP)) {
                     // should only happen for ibgp
                     String nextHopInterface = remoteRoute
                           .getNextHopInterface();
                     Prefix nextHopPrefix = remoteVrf.getInterfaces()
                           .get(nextHopInterface).getPrefix();
                     if (nextHopPrefix == null) {
                        throw new BatfishException(
                              "remote route's nextHopInterface has no address");
                     }
                     nextHopIp = nextHopPrefix.getAddress();
                  }
                  transformedOutgoingRouteBuilder.setNextHopIp(nextHopIp);
                  transformedOutgoingRouteBuilder
                        .setLocalPreference(localPreference);

                  // Outgoing srcProtocol
                  transformedOutgoingRouteBuilder
                        .setSrcProtocol(remoteRoute.getProtocol());

                  /*
                   * CREATE OUTGOING ROUTE
                   */
                  boolean acceptOutgoing = remoteExportPolicy.process(
                        remoteRoute, transformedOutgoingRouteBuilder, localIp,
                        remoteVrfName);
                  if (acceptOutgoing) {
                     BgpRoute transformedOutgoingRoute = transformedOutgoingRouteBuilder
                           .build();
                     // Record sent advertisement
                     BgpAdvertisementType sentType = ebgpSession
                           ? BgpAdvertisementType.EBGP_SENT
                           : BgpAdvertisementType.IBGP_SENT;
                     Ip sentOriginatorIp = transformedOutgoingRoute
                           .getOriginatorIp();
                     SortedSet<Long> sentClusterList = new TreeSet<>(
                           transformedOutgoingRoute.getClusterList());
                     boolean sentReceivedFromRouteReflectorClient = transformedOutgoingRoute
                           .getReceivedFromRouteReflectorClient();
                     AsPath sentAsPath = transformedOutgoingRoute.getAsPath();
                     SortedSet<Long> sentCommunities = new TreeSet<>(
                           transformedOutgoingRoute.getCommunities());
                     Prefix sentNetwork = remoteRoute.getNetwork();
                     Ip sentNextHopIp;
                     String sentSrcNode = remoteHostname;
                     String sentSrcVrf = remoteVrfName;
                     Ip sentSrcIp = remoteBgpNeighbor.getLocalIp();
                     String sentDstNode = hostname;
                     String sentDstVrf = _vrf.getName();
                     Ip sentDstIp = neighbor.getLocalIp();
                     int sentWeight = -1;
                     if (ebgpSession) {
                        sentNextHopIp = nextHopIp;
                     }
                     else {
                        sentNextHopIp = transformedOutgoingRoute.getNextHopIp();
                     }
                     int sentLocalPreference = transformedOutgoingRoute
                           .getLocalPreference();
                     int sentMed = transformedOutgoingRoute.getMetric();
                     OriginType sentOriginType = transformedOutgoingRoute
                           .getOriginType();
                     RoutingProtocol sentSrcProtocol = targetProtocol;
                     BgpRoute.Builder transformedIncomingRouteBuilder = new BgpRoute.Builder();

                     // Incoming originatorIp
                     transformedIncomingRouteBuilder
                           .setOriginatorIp(sentOriginatorIp);

                     // Incoming clusterList
                     transformedIncomingRouteBuilder.getClusterList()
                           .addAll(sentClusterList);

                     // Incoming receivedFromRouteReflectorClient
                     transformedIncomingRouteBuilder
                           .setReceivedFromRouteReflectorClient(
                                 sentReceivedFromRouteReflectorClient);

                     // Incoming asPath
                     transformedIncomingRouteBuilder
                           .setAsPath(sentAsPath.getAsSets());

                     // Incoming communities
                     transformedIncomingRouteBuilder.getCommunities()
                           .addAll(sentCommunities);

                     // Incoming protocol
                     transformedIncomingRouteBuilder
                           .setProtocol(targetProtocol);

                     // Incoming network
                     transformedIncomingRouteBuilder.setNetwork(sentNetwork);

                     // Incoming nextHopIp
                     transformedIncomingRouteBuilder
                           .setNextHopIp(sentNextHopIp);

                     // Incoming localPreference
                     transformedIncomingRouteBuilder
                           .setLocalPreference(sentLocalPreference);

                     // Incoming admin
                     int admin = ebgpSession ? ebgpAdmin : ibgpAdmin;
                     transformedIncomingRouteBuilder.setAdmin(admin);

                     // Incoming metric
                     transformedIncomingRouteBuilder.setMetric(sentMed);

                     // Incoming originType
                     transformedIncomingRouteBuilder
                           .setOriginType(sentOriginType);

                     // Incoming srcProtocol
                     transformedIncomingRouteBuilder
                           .setSrcProtocol(sentSrcProtocol);
                     String importPolicyName = neighbor.getImportPolicy();
                     // TODO: ensure there is always an import policy

                     if (ebgpSession
                           && transformedOutgoingRoute.getAsPath()
                           .containsAs(neighbor.getLocalAs())
                           && !neighbor.getAllowLocalAsIn()) {
                        // skip routes containing peer's AS unless
                        // disable-peer-as-check (getAllowRemoteAsOut) is set
                        continue;
                     }

                     BgpAdvertisement sentAdvert = new BgpAdvertisement(
                           sentType, sentNetwork, sentNextHopIp, sentSrcNode,
                           sentSrcVrf, sentSrcIp, sentDstNode, sentDstVrf,
                           sentDstIp, sentSrcProtocol, sentOriginType,
                           sentLocalPreference, sentMed, sentOriginatorIp,
                           sentAsPath, new TreeSet<>(sentCommunities),
                           new TreeSet<>(sentClusterList), sentWeight);
                     _sentBgpAdvertisements.add(sentAdvert);

                     /*
                      * CREATE INCOMING ROUTE
                      */
                     boolean acceptIncoming = true;
                     if (importPolicyName != null) {
                        RoutingPolicy importPolicy = _c.getRoutingPolicies()
                              .get(importPolicyName);
                        if (importPolicy != null) {
                           acceptIncoming = importPolicy.process(
                                 transformedOutgoingRoute,
                                 transformedIncomingRouteBuilder,
                                 remoteBgpNeighbor.getLocalIp(), _key);
                        }
                     }
                     if (acceptIncoming) {
                        BgpRoute transformedIncomingRoute = transformedIncomingRouteBuilder
                              .build();
                        BgpAdvertisementType receivedType = ebgpSession
                              ? BgpAdvertisementType.EBGP_RECEIVED
                              : BgpAdvertisementType.IBGP_RECEIVED;
                        Prefix receivedNetwork = sentNetwork;
                        Ip receivedNextHopIp = sentNextHopIp;
                        String receivedSrcNode = sentSrcNode;
                        String receivedSrcVrf = sentSrcVrf;
                        Ip receivedSrcIp = sentSrcIp;
                        String receivedDstNode = sentDstNode;
                        String receivedDstVrf = sentDstVrf;
                        Ip receivedDstIp = sentDstIp;
                        RoutingProtocol receivedSrcProtocol = sentSrcProtocol;
                        OriginType receivedOriginType = transformedIncomingRoute
                              .getOriginType();
                        int receivedLocalPreference = transformedIncomingRoute
                              .getLocalPreference();
                        int receivedMed = transformedIncomingRoute.getMetric();
                        Ip receivedOriginatorIp = sentOriginatorIp;
                        AsPath receivedAsPath = transformedIncomingRoute
                              .getAsPath();
                        SortedSet<Long> receivedCommunities = new TreeSet<>(
                              transformedIncomingRoute.getCommunities());
                        SortedSet<Long> receivedClusterList = new TreeSet<>(
                              sentClusterList);
                        int receivedWeight = transformedIncomingRoute
                              .getWeight();
                        BgpAdvertisement receivedAdvert = new BgpAdvertisement(
                              receivedType, receivedNetwork, receivedNextHopIp,
                              receivedSrcNode, receivedSrcVrf, receivedSrcIp,
                              receivedDstNode, receivedDstVrf, receivedDstIp,
                              receivedSrcProtocol, receivedOriginType,
                              receivedLocalPreference, receivedMed,
                              receivedOriginatorIp, receivedAsPath,
                              new TreeSet<>(receivedCommunities),
                              new TreeSet<>(receivedClusterList),
                              receivedWeight);
                        _receivedBgpAdvertisements.add(receivedAdvert);

                        if (targetRib.mergeRoute(transformedIncomingRoute)) {
                           numRoutes++;
                        }
                     }
                  }
               }
            }
         }
      }
      return numRoutes;
   }

   public boolean propagateOspfExternalRoutes(
         Map<String, Node> nodes,
         Topology topology) {
      boolean changed = false;
      String node = _c.getHostname();
      if (_vrf.getOspfProcess() != null) {
         int admin = RoutingProtocol.OSPF
               .getDefaultAdministrativeCost(_c.getConfigurationFormat());
         EdgeSet edges = topology.getNodeEdges().get(node);
         if (edges == null) {
            // there are no edges, so OSPF won't produce anything
            return false;
         }
         for (Edge edge : edges) {
            if (!edge.getNode1().equals(node)) {
               continue;
            }
            String connectingInterfaceName = edge.getInt1();
            Interface connectingInterface = _vrf.getInterfaces()
                  .get(connectingInterfaceName);
            if (connectingInterface == null) {
               // wrong vrf, so skip
               continue;
            }
            String neighborName = edge.getNode2();
            Node neighbor = nodes.get(neighborName);
            String neighborInterfaceName = edge.getInt2();
            OspfArea area = connectingInterface.getOspfArea();
            Configuration nc = neighbor._c;
            Interface neighborInterface = nc.getInterfaces()
                  .get(neighborInterfaceName);
            String neighborVrfName = neighborInterface.getVrfName();
            VirtualRouter neighborVirtualRouter = _nodes
                  .get(neighborName)._virtualRouters.get(neighborVrfName);

            OspfArea neighborArea = neighborInterface.getOspfArea();
            if (connectingInterface.getOspfEnabled()
                  && !connectingInterface.getOspfPassive()
                  && neighborInterface.getOspfEnabled()
                  && !neighborInterface.getOspfPassive() && area != null
                  && neighborArea != null) {
               /*
                * We have an ospf neighbor relationship on this edge. So we
                * should add all ospf external type 1(2) routes from this
                * neighbor into our ospf external type 1(2) staging rib. For
                * type 1, the cost of the route increases each time. For type 2,
                * the cost remains constant, but we must keep track of cost to
                * advertiser as a tie-breaker.
                */
               int connectingInterfaceCost = connectingInterface.getOspfCost();
               for (OspfExternalType1Route neighborRoute : neighborVirtualRouter._prevOspfExternalType1Rib
                     .getRoutes()) {
                  int newMetric = neighborRoute.getMetric()
                        + connectingInterfaceCost;
                  int newCostToAdvertiser = neighborRoute.getCostToAdvertiser()
                        + connectingInterfaceCost;
                  OspfExternalType1Route newRoute = new OspfExternalType1Route(
                        neighborRoute.getNetwork(),
                        neighborInterface.getPrefix().getAddress(), admin,
                        newMetric, newCostToAdvertiser,
                        neighborRoute.getAdvertiser());
                  if (_ospfExternalType1StagingRib.mergeRoute(newRoute)) {
                     changed = true;
                  }
               }
               for (OspfExternalType2Route neighborRoute : neighborVirtualRouter._prevOspfExternalType2Rib
                     .getRoutes()) {
                  int newCostToAdvertiser = neighborRoute.getCostToAdvertiser()
                        + connectingInterfaceCost;
                  OspfExternalType2Route newRoute = new OspfExternalType2Route(
                        neighborRoute.getNetwork(),
                        neighborInterface.getPrefix().getAddress(), admin,
                        neighborRoute.getMetric(), newCostToAdvertiser,
                        neighborRoute.getAdvertiser());
                  if (_ospfExternalType2StagingRib.mergeRoute(newRoute)) {
                     changed = true;
                  }
               }
            }
         }
      }
      return changed;
   }

   public boolean propagateOspfInternalRoutes(
         Map<String, Node> nodes,
         Topology topology) {
      boolean changed = false;
      String node = _c.getHostname();
      if (_vrf.getOspfProcess() != null) {
         int admin = RoutingProtocol.OSPF
               .getDefaultAdministrativeCost(_c.getConfigurationFormat());
         EdgeSet edges = topology.getNodeEdges().get(node);
         if (edges == null) {
            // there are no edges, so OSPF won't produce anything
            return false;
         }
         for (Edge edge : edges) {
            if (!edge.getNode1().equals(node)) {
               continue;
            }
            String connectingInterfaceName = edge.getInt1();
            Interface connectingInterface = _vrf.getInterfaces()
                  .get(connectingInterfaceName);
            if (connectingInterface == null) {
               // wrong vrf, so skip
               continue;
            }
            String neighborName = edge.getNode2();
            Node neighbor = nodes.get(neighborName);
            String neighborInterfaceName = edge.getInt2();
            OspfArea area = connectingInterface.getOspfArea();
            Configuration nc = neighbor._c;
            Interface neighborInterface = nc.getInterfaces()
                  .get(neighborInterfaceName);
            String neighborVrfName = neighborInterface.getVrfName();
            VirtualRouter neighborVirtualRouter = _nodes
                  .get(neighborName)._virtualRouters.get(neighborVrfName);
            OspfArea neighborArea = neighborInterface.getOspfArea();
            if (connectingInterface.getOspfEnabled()
                  && !connectingInterface.getOspfPassive()
                  && neighborInterface.getOspfEnabled()
                  && !neighborInterface.getOspfPassive() && area != null
                  && neighborArea != null) {

               if (area.getName().equals(neighborArea.getName())) {
                  /*
                   * We have an ospf intra-area neighbor relationship on this
                   * edge. So we should add all ospf routes from this neighbor
                   * into our ospf intra-area staging rib, adding the cost of
                   * the connecting interface, and using the neighborInterface's
                   * address as the next hop ip
                   */
                  int connectingInterfaceCost = connectingInterface
                        .getOspfCost();
                  long areaNum = area.getName();
                  for (OspfIntraAreaRoute neighborRoute : neighborVirtualRouter._ospfIntraAreaRib
                        .getRoutes()) {
                     int newCost = neighborRoute.getMetric()
                           + connectingInterfaceCost;
                     Ip nextHopIp = neighborInterface.getPrefix().getAddress();
                     OspfIntraAreaRoute newRoute = new OspfIntraAreaRoute(
                           neighborRoute.getNetwork(), nextHopIp, admin,
                           newCost, areaNum);
                     if (_ospfIntraAreaStagingRib.mergeRoute(newRoute)) {
                        changed = true;
                     }
                  }
                  // we also propagate inter-area routes that have already made
                  // it into this area, unless they originate in this area
                  for (OspfInterAreaRoute neighborRoute : neighborVirtualRouter._ospfInterAreaRib
                        .getRoutes()) {
                     long neighborRouteArea = neighborRoute.getArea();
                     if (neighborRouteArea != areaNum) {
                        Prefix neighborRouteNetwork = neighborRoute
                              .getNetwork();
                        String neighborSummaryFilterName = neighborArea
                              .getSummaryFilter();
                        boolean hasSummaryFilter = neighborSummaryFilterName != null;
                        boolean allowed = !hasSummaryFilter;
                        if (hasSummaryFilter) {
                           RouteFilterList neighborSummaryFilter = neighbor._c
                                 .getRouteFilterLists()
                                 .get(neighborSummaryFilterName);
                           allowed = neighborSummaryFilter
                                 .permits(neighborRouteNetwork);
                        }
                        if (allowed) {
                           int newCost = neighborRoute.getMetric()
                                 + connectingInterfaceCost;
                           Ip nextHopIp = neighborInterface.getPrefix()
                                 .getAddress();
                           OspfInterAreaRoute newRoute = new OspfInterAreaRoute(
                                 neighborRouteNetwork, nextHopIp, admin,
                                 newCost, areaNum);
                           if (_ospfInterAreaStagingRib.mergeRoute(newRoute)) {
                              changed = true;
                           }
                        }
                     }
                  }
               }
               else if (area.getName().equals(0l)
                     || neighborArea.getName().equals(0l)) {
                  /*
                   * We have an ospf inter-area neighbor relationship on this
                   * edge. So we should add all ospf routes from this neighbor
                   * into our ospf inter-area staging rib, adding the cost of
                   * the connecting interface, and using the neighborInterface's
                   * address as the next hop ip
                   *
                   */
                  int connectingInterfaceCost = connectingInterface
                        .getOspfCost();
                  long areaNum = area.getName();
                  // inter-area routes can only be sent FROM area 0 when sender
                  // is in different area, unless the route is from the
                  // neighbor's area
                  for (OspfInterAreaRoute neighborRoute : neighborVirtualRouter._ospfInterAreaRib
                        .getRoutes()) {
                     // do not receive inter-area routes that originally came
                     // from this area
                     long neighborRouteArea = neighborRoute.getArea();
                     if (areaNum != neighborRouteArea
                           && (neighborArea.getName().equals(0l) || neighborArea
                           .getName().equals(neighborRouteArea))) {
                        Prefix neighborRouteNetwork = neighborRoute
                              .getNetwork();
                        String neighborSummaryFilterName = neighborArea
                              .getSummaryFilter();
                        boolean hasSummaryFilter = neighborSummaryFilterName != null;
                        boolean allowed = !hasSummaryFilter;
                        if (hasSummaryFilter) {
                           RouteFilterList neighborSummaryFilter = neighbor._c
                                 .getRouteFilterLists()
                                 .get(neighborSummaryFilterName);
                           allowed = neighborSummaryFilter
                                 .permits(neighborRouteNetwork);
                        }
                        if (allowed) {
                           int newCost = neighborRoute.getMetric()
                                 + connectingInterfaceCost;
                           Ip nextHopIp = neighborInterface.getPrefix()
                                 .getAddress();
                           OspfIntraAreaRoute newRoute = new OspfIntraAreaRoute(
                                 neighborRouteNetwork, nextHopIp, admin,
                                 newCost, areaNum);
                           if (_ospfIntraAreaStagingRib.mergeRoute(newRoute)) {
                              changed = true;
                           }
                        }

                     }
                  }
                  // intra-area routes may be turned into inter-area routes
                  // going either to or from area 0
                  for (OspfInterAreaRoute neighborRoute : neighborVirtualRouter._ospfInterAreaRib
                        .getRoutes()) {
                     String neighborSummaryFilterName = neighborArea
                           .getSummaryFilter();
                     boolean hasSummaryFilter = neighborSummaryFilterName != null;
                     boolean allowed = !hasSummaryFilter;
                     Prefix neighborRouteNetwork = neighborRoute.getNetwork();
                     if (hasSummaryFilter) {
                        RouteFilterList neighborSummaryFilter = neighbor._c
                              .getRouteFilterLists()
                              .get(neighborSummaryFilterName);
                        allowed = neighborSummaryFilter
                              .permits(neighborRouteNetwork);
                     }
                     if (allowed) {
                        int newCost = neighborRoute.getMetric()
                              + connectingInterfaceCost;
                        Ip nextHopIp = neighborInterface.getPrefix()
                              .getAddress();
                        OspfInterAreaRoute newRoute = new OspfInterAreaRoute(
                              neighborRouteNetwork, nextHopIp, admin, newCost,
                              areaNum);
                        if (_ospfInterAreaStagingRib.mergeRoute(newRoute)) {
                           changed = true;
                        }
                     }
                  }
               }
            }
         }
      }
      return changed;
   }

   public void unstageBgpRoutes() {
      importRib(_ebgpMultipathRib, _ebgpStagingRib);
      importRib(_ebgpBestPathRib, _ebgpStagingRib);
      importRib(_ibgpMultipathRib, _ibgpStagingRib);
      importRib(_ibgpBestPathRib, _ibgpStagingRib);
   }

   public void unstageOspfExternalRoutes() {
      importRib(_ospfExternalType1Rib, _ospfExternalType1StagingRib);
      importRib(_ospfExternalType2Rib, _ospfExternalType2StagingRib);
   }

   public void unstageOspfInternalRoutes() {
      for (OspfIntraAreaRoute route : _ospfIntraAreaStagingRib.getRoutes()) {
         _ospfIntraAreaRib.mergeRoute(route);
      }
      for (OspfInterAreaRoute route : _ospfInterAreaStagingRib.getRoutes()) {
         _ospfInterAreaRib.mergeRoute(route);
      }
   }

}
