package org.batfish.common.plugin;

import org.batfish.common.Answerer;
import org.batfish.datamodel.*;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.answers.ConvertConfigurationAnswerElement;
import org.batfish.datamodel.answers.InitInfoAnswerElement;
import org.batfish.datamodel.answers.ParseVendorConfigurationAnswerElement;
import org.batfish.datamodel.assertion.AssertionAst;
import org.batfish.datamodel.collections.*;
import org.batfish.datamodel.questions.Question;

import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.BiFunction;
import java.util.regex.Pattern;

public interface IBatfish extends IPluginConsumer {

   AnswerElement answerAclReachability(String aclNameRegexStr,
         NamedStructureEquivalenceSets<?> aclEqSets);

   void checkConfigurations();

   void checkDataPlane();

   void checkDataPlaneQuestionDependencies();

   void checkEnvironmentExists();

   InterfaceSet computeFlowSinks(Map<String, Configuration> configurations,
         boolean differentialContext, Topology topology);

   Map<Ip, Set<String>> computeIpOwners(
         Map<String, Configuration> configurations);

   Topology computeTopology(Map<String, Configuration> configurations);

   AnswerElement createEnvironment(String environmentName,
         NodeSet nodeBlacklist, Set<NodeInterfacePair> interfaceBlacklist,
         boolean dp);


   AnswerElement smtForwarding(HeaderSpace h);

   AnswerElement smtReachability(HeaderSpace h,
           String ingressNodeRegexStr, String notIngressNodeRegexStr,
           String finalNodeRegexStr, String notFinalNodeRegexStr,
           String finalIfaceRegexStr, String notFinalIfaceRegexStr);

   AnswerElement smtBlackhole();

   AnswerElement smtRoutingLoop();

   AnswerElement smtBoundedLength(HeaderSpace h,
           String ingressNodeRegexStr, String notIngressNodeRegexStr,
           String finalNodeRegexStr, String notFinalNodeRegexStr,
           String finalIfaceRegexStr, String notFinalIfaceRegexStr, Integer bound);

   AnswerElement smtEqualLength(HeaderSpace h,
           String ingressNodeRegexStr, String notIngressNodeRegexStr,
           String finalNodeRegexStr, String notFinalNodeRegexStr,
           String finalIfaceRegexStr, String notFinalIfaceRegexStr);

   AnswerElement smtMultipathConsistency(HeaderSpace h,
           String finalNodeRegexStr, String notFinalNodeRegexStr,
           String finalIfaceRegexStr, String notFinalIfaceRegexStr);

   AnswerElement smtLoadBalance(HeaderSpace h,
           String ingressNodeRegexStr, String notIngressNodeRegexStr,
           String finalNodeRegexStr, String notFinalNodeRegexStr,
           String finalIfaceRegexStr, String notFinalIfaceRegexStr, int threshold);

   AnswerElement smtLocalConsistency(Pattern routerRegex);


   Map<String, BiFunction<Question, IBatfish, Answerer>> getAnswererCreators();

   ConvertConfigurationAnswerElement getConvertConfigurationAnswerElement();

   String getDifferentialFlowTag();

   String getFlowTag();

   FlowHistory getHistory();

   ParseVendorConfigurationAnswerElement getParseVendorConfigurationAnswerElement();

   void initBgpAdvertisements(Map<String, Configuration> configurations);

   void initBgpOriginationSpaceExplicit(
         Map<String, Configuration> configurations);

   InitInfoAnswerElement initInfo(boolean summary);

   void initRemoteBgpNeighbors(Map<String, Configuration> configurations,
         Map<Ip, Set<String>> ipOwners);

   void initRemoteIpsecVpns(Map<String, Configuration> configurations);

   void initRoutes(Map<String, Configuration> configurations);

   Map<String, Configuration> loadConfigurations();

   DataPlane loadDataPlane();

   AnswerElement multipath(HeaderSpace headerSpace);

   AtomicInteger newBatch(String description, int jobs);

   AssertionAst parseAssertion(String text);

   AnswerElement pathDiff(HeaderSpace headerSpace);

   void popEnvironment();

   void printElapsedTime();

   AdvertisementSet processExternalBgpAnnouncements(
         Map<String, Configuration> configurations);

   void processFlows(Set<Flow> flows);

   void pushBaseEnvironment();

   void pushDeltaEnvironment();

   AnswerElement reducedReachability(HeaderSpace headerSpace);

   void registerAnswerer(String questionClassName,
         BiFunction<Question, IBatfish, Answerer> answererCreator);

   void resetTimer();

   void setDataPlanePlugin(DataPlanePlugin dataPlanePlugin);

   AnswerElement standard(HeaderSpace headerSpace,
         Set<ForwardingAction> actions, String ingressNodeRegexStr,
         String notIngressNodeRegexStr, String finalNodeRegexStr,
         String notFinalNodeRegexStr);

   void writeDataPlane(DataPlane dp);

}
