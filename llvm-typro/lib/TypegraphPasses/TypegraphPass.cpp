#include "TypegraphPass.h"
#include "../Typegraph/TGDispatcherBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Typegraph/TGCallGraph.h"
#include "llvm/Typegraph/Typegraph.h"
#include "llvm/Typegraph/TypegraphSettings.h"
#include "llvm/Typegraph/timeclock.h"
#include "llvm/Typegraph/typegraph_llvm_utils.h"
#include "llvm/Analysis/CallGraph.h"
#include <chrono>
#include <llvm/Bitcode/BitcodeWriter.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/Support/JSON.h>
#include <llvm/Typegraph/typegraph_layering.h>
#include <fstream>
#include "llvm/IR/CFG.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <vector>
#include <set>
#include <iostream>
#include <fstream>
#include <list>
#include <algorithm>
#include "llvm/Support/FormatVariadic.h"



using namespace typegraph;

namespace llvm {

  namespace {
        // Data structures for the graph
struct Node {
    std::string name;
    llvm::BasicBlock *BB;
    std::string FunctionName;
 
    // Default constructor
    Node() : name(""), BB(nullptr), FunctionName("") {}
 
    // Parameterized constructor
    Node(const std::string &n, llvm::BasicBlock *bb, const std::string &fn)
        : name(n), BB(bb), FunctionName(fn) {}
};
 
struct Edge {
    llvm::BasicBlock *from; //
    llvm::BasicBlock *to;
    std::string edgeType; // [Inter,Intra,return]
    Edge() : from(nullptr), to(nullptr), edgeType("") {}
    Edge(llvm::BasicBlock *from, llvm::BasicBlock *to, const std::string &edgeType)
        : from(from), to(to), edgeType(edgeType) {}
 
 
   // Overload the equality operator for comparison
    bool operator==(const Edge &other) const {
        return from == other.from && to == other.to;
    }
 
    // Overload the less-than operator for sorting and ordering in a set
    bool operator<(const Edge &other) const {
        if (from != other.from)
            return from < other.from;
        return to < other.to;
    }
};
 
 
struct InterproceduralGraph {
    std::map<llvm:: BasicBlock*, Node> nodes;
    std::vector<Edge> edges;
    std::list<llvm::BasicBlock*> intermadiateAddr;
    std::set<std::string> functionsWithIndirectCalls;
    std::list<llvm::BasicBlock*> addrPointer;
    llvm::BasicBlock* getSig(const Node &node) {
    return node.BB;
    }
    void addNode(const Node &node) {
        llvm::BasicBlock* sig = getSig(node);
        nodes[sig] = node;
    }
 
   void addEdge(const Edge &edge) {
        // Check if the edge is already in the vector
        if (std::find(edges.begin(), edges.end(), edge) == edges.end()) {
            edges.push_back(edge);
        }
    }
 
    void addIntraproceduralEdges(Function &F){
         for (BasicBlock &BB : F) {
            Node BBNode = Node(BB.getName().str(), &BB, F.getName().str());
            addNode(BBNode);
           if (std::find(intermadiateAddr.begin(), intermadiateAddr.end(), &BB) == intermadiateAddr.end()) {
            intermadiateAddr.push_back(&BB);
            addrPointer.push_back(&BB);
           }
            BasicBlock* BBSig = getSig(BBNode);
            // Iterate over each successor of the basic block
            for (BasicBlock *Succ : successors(&BB)) {
                Node SuccNode = Node(Succ->getName().str(), Succ, F.getName().str());
                addNode(SuccNode);
                // If the successor's address is not already in intermadiateAddr, add it
                if (std::find(intermadiateAddr.begin(), intermadiateAddr.end(), Succ) == intermadiateAddr.end()) {
                        intermadiateAddr.push_back(Succ);
                        addrPointer.push_back(Succ);
                }
                BasicBlock* succSig = getSig(SuccNode);
                Edge intraEdge = Edge(BBSig, succSig, "Intra");
                addEdge(intraEdge);
            }
        }
    }
 
    void addInterproceduralEdges(CallGraph &CG) {
        bool found = false;
        for (auto &nodePair : CG) {
            const Function *caller = nodePair.first;
            CallGraphNode *cgn = nodePair.second.get();
            if (caller){
            for (auto it = cgn->begin(); it != cgn->end(); ++it) {
                found = false;
                CallGraphNode::CallRecord callRecord = *it;
                Function *callee = callRecord.second->getFunction();
                if (callee) {
                        for (const BasicBlock &CBB : *caller) {
                                for (const Instruction &I : CBB) {
                                        if (const CallBase *CB = dyn_cast<CallBase>(&I)) {
                                        if (CB->getCalledFunction() == callee) {
                                                llvm::BasicBlock *CBBPtr = const_cast<llvm::BasicBlock*>(&CBB);
                                        Node callerNode = Node(CBB.getName().str(), CBBPtr, caller->getName().str());
                                        llvm::BasicBlock* callersig = getSig(callerNode);
                                        addNode(callerNode);
                                        if (std::find(intermadiateAddr.begin(), intermadiateAddr.end(), CBBPtr) == intermadiateAddr.end()){
                                        intermadiateAddr.push_back(CBBPtr);
                                        addrPointer.push_back(CBBPtr);
                                        }
 
                                        //addEdge(caller->getName().str(), callee->getName().str());
                                        if (callee && !callee->isDeclaration()) {
                                                for (BasicBlock &calleeBB : *callee){
                                                        for (Instruction &I : calleeBB){
                                                                if (isa<llvm::ReturnInst>(&I)) {
                                                                        found = true;
 
                                                Node calleeNode = Node(calleeBB.getName().str(), &calleeBB, callee->getName().str());
                                                BasicBlock* calleesig = getSig(calleeNode);
                                                addNode(calleeNode);
                                                if (std::find(intermadiateAddr.begin(), intermadiateAddr.end(), &calleeBB) == intermadiateAddr.end()){
                                                        intermadiateAddr.push_back(&calleeBB);
                                                        addrPointer.push_back(&calleeBB);
                                                }
                                                Edge interEdge = Edge(callersig, calleesig, "Inter");
                                                addEdge(interEdge);
                                                break;
                                                }
                                                if (found)
                                                break;
                                        }
                                        if (found)
                                        break;
                                }
                                if (found)
                                break;
                        }
                            }
                        }
                        if(found)
                        break;
                    }
                    if(found)
                    break;
                }
            }
            }
            }
        }
    }
 
 
    std::set<std::string> getPossibleIndirectTargets(const std::string &FuncName) {
        return std::set<std::string>();
    }
 
 void outputGraph() {
        // errs() << "Nodes:\n";
        // for (const auto &NodePair : nodes) {
        //     errs() << "  " << NodePair.first << "\n";
        // }
 
        // errs() << "Edges:\n";
        // for (const auto &Edge : edges) {
        //     errs() << "  " << Edge.from << " -> " << Edge.to << ":" <<Edge.edgeType <<"\n";
        // }
        return;
    }
bool writeGraph() {
        // Create an output file stream object to write to a file
    std::ofstream outFile("/home/isec/TyPro-CFI/build/test/intermediate.txt");
 
    // Check if the file opened successfully
    if (!outFile) {
        return false;
    }
 
    // Write the list elements to the file
    for (llvm::BasicBlock* addr : intermadiateAddr) {
        std::string bbAddress = llvm::formatv("{0}", static_cast<const void*>(addr)).str();
        outFile << bbAddress << std::endl;  // Each value on a new line
    }
    // Close the file
    outFile.close();
    return true;
}
 
};

void insertAddrListtoSection(Module &M, std::list<llvm::BasicBlock*> addrs) {
    LLVMContext &Context = M.getContext();
    Type *Int64Ty = Type::getInt64Ty(Context);
    IRBuilder<> Builder(Context);
    for (const auto &addr : addrs) {
        outs() << "Processing basic block at address " << addr << "\n";
 
        // Get a Constant that represents the address of the basic block
        Constant *blockAddr = BlockAddress::get(addr->getParent(), addr);
 
        // // Convert the block address to an integer
        // Value *addrValue = ConstantExpr::getPtrToInt(blockAddr, Int64Ty);
        Builder.SetInsertPoint(addr);
        Value *result = Builder.CreatePtrToInt(blockAddr, Type::getInt64Ty(Context));
        Constant *resultConstant = dyn_cast<Constant>(result);
            if (!resultConstant) {
              llvm::errs() << "convert failed"<< "\n";
            }
        // Create a global variable with the integer value
        GlobalVariable *MyVariable = new GlobalVariable(
            M,                       // Module
            Int64Ty,                 // Type
            false,                   // IsConstant
            GlobalValue::ExternalLinkage, // Linkage
            resultConstant, // Initializer
            "myVariable",            // Name
            nullptr,                 // InsertBefore
            GlobalValue::NotThreadLocal, // Thread Local
            0,                       // AddressSpace
            true                     // Constant
        );
 
        // Set the section where the global variable should be placed
        MyVariable->setSection(".section_for_address");
    }
    return;
}
// Helper function that does the actual graph construction and output
bool interproceduralGraphImpl(Module &M, CallGraph &CG) {
    InterproceduralGraph IPG;
 
    for (Function &F : M) {
        IPG.addIntraproceduralEdges(F);
    }
    IPG.addInterproceduralEdges(CG);
//     IPG.addIndirectCallEdges();
    IPG.outputGraph();
    if (!IPG.writeGraph()){
         errs() << "Error: Could not open the file for writing!" << "\n";
    }
    insertAddrListtoSection(M,IPG.intermadiateAddr);
    return true;
}
}
 

class TypeGraphPassInternal {
  TimeClock Clock;
  Module &M;
  CallGraph &CG;
  TypeGraph Graph;

public:
  TypeGraphPassInternal(Module &M, CallGraph &CG) : M(M), CG(CG) {
    if (Settings.enabled) {
      // Fix paths
      if (Settings.graph_output && std::string(Settings.graph_output) == "auto") {
        Settings.graph_output = Settings.output_filename.c_str();
      }
      if (Settings.tgcfi_output && std::string(Settings.tgcfi_output) == "auto") {
        Settings.tgcfi_output = (new std::string(Settings.output_filename + ".tgcfi.json"))->c_str();
        Settings.ordered_json_object_name = (new std::string(Settings.output_filename + ".txt"))->c_str();
      }
      if (Settings.output_filename.substr(0, 9) == "conftest-") {
        Settings.graph_output = nullptr;
        Settings.tgcfi_output = nullptr;
      }
    }
  }

  ~TypeGraphPassInternal() {
    if (Settings.enabled) {
      Clock.report("Typegraph combined");
    }
  }

  // void writeCallTargetOutput() {
  //   llvm::json::Object J;
  //   J["tg_targets"] = llvm::json::Object();
  //   J["tg_targets_hash"] = llvm::json::Object();
  //   J["tg_targets_argnum"] = llvm::json::Object();
  //   auto *CallMap = J.getObject("tg_targets");
  //   auto *CallMapHash = J.getObject("tg_targets_hash");
  //   auto *CallMapArgnum = J.getObject("tg_targets_argnum");
  //   LLVMContext &Context = M.getContext();
  //   IRBuilder<> Builder(Context);
  //   //create a vector for callName
  //   std::vector<llvm::StringRef> CallNameVec;
  //   for (auto &F : M.functions()) {
  //     for (auto &Bb : F) {
  //       for (auto &Ins : Bb) {
  //         if (auto *Call = dyn_cast<CallBase>(&Ins)) {
  //           if (!Call->isIndirectCall())
  //             continue;
  //           auto *TypegraphNode = Ins.getMetadata(LLVMContext::MD_typegraph_node);
  //           assert(TypegraphNode);
  //           auto CallName = cast<MDString>(TypegraphNode->getOperand(0))->getString();
  //           (*CallMap)[CallName] = llvm::json::Array();
  //           auto *Arr = CallMap->getArray(CallName);
  //           (*CallMapHash)[CallName] = llvm::json::Array();
  //           auto *HashArr = CallMapHash->getArray(CallName);
  //           (*CallMapArgnum)[CallName] = llvm::json::Array();
  //           auto *ArrArgNum = CallMapArgnum->getArray(CallName);
  //           for (auto &In: Bb) {
  //             HashArr->push_back(In.getOpcodeName());
  //           }
  //           CallNameVec.push_back(CallName);
  //           // llvm::errs() << "Indirect Call Function name: " << F.getName() << "\n";
  //           BlockAddress *blockAddress = BlockAddress::get(&F, &Bb);
  //           // llvm::errs() << "BA:" << blockAddress << "\n";
  //           Builder.SetInsertPoint(&Bb);
  //           Value *result = Builder.CreatePtrToInt(blockAddress, Type::getInt64Ty(Context));
  //           // llvm::errs() << "result:" << result << "\n";
  //           Constant *resultConstant = dyn_cast<Constant>(result);
  //           if (!resultConstant) {
  //             // llvm::errs() << "convert failed"<< "\n";
  //           }
  //           // llvm::errs() << "resultConstant:" << resultConstant << "\n";
  //           GlobalVariable *MyVariable =
  //               new GlobalVariable(M, Type::getInt64Ty(Context), false, GlobalValue::ExternalLinkage, resultConstant,
  //                                  "myVariable", nullptr, GlobalValue::NotThreadLocal, 0, true);
  //           // llvm::errs() << "Setting section for MyVariable\n";
  //           MyVariable->setSection(".section_for_indirectcall");
  //           for (auto &Use : getFunctionUsesForIndirectCall(Call)) {
  //             if (Use.Function) {
  //               Arr->push_back(Use.Function->getName());
  //               if (isArgnumCompatible(Call, Use.Function)) {
  //                 ArrArgNum->push_back(Use.Function->getName());
  //               }
  //             }
  //           }
  //           std::sort(Arr->begin(), Arr->end(), [](json::Value &V1, json::Value&V2) { return V1.getAsString().getValue() < V2.getAsString().getValue(); });
  //           std::sort(ArrArgNum->begin(), ArrArgNum->end(), [](json::Value &V1, json::Value&V2) { return V1.getAsString().getValue() < V2.getAsString().getValue(); });
  //         }
  //       }
  //     }
  //   }
    // std::error_code EC;
  //   llvm::raw_fd_ostream output_file(Settings.ordered_json_object_name, EC, sys::fs::F_Text);

  //   // Write data to the file
  //   for (const auto &value : CallNameVec) {
  //     output_file << value << "\n";
  //   }
  //   llvm::raw_fd_ostream File(Settings.tgcfi_output, EC);
  //   File << llvm::json::Value(std::move(J)) << "\n";
  // }
  
  bool run() {
    if (!Settings.enabled) {
      llvm::errs() << "[Setting] TG_ENABLED = false\n";
      return false;
    } 
    Clock.report("Before interproceduralGraphImpl");
    return interproceduralGraphImpl(M,CG);
  }
};

PreservedAnalyses TypeGraphPass::run(Module &M, ModuleAnalysisManager &MAM) {
  CallGraph &CG = MAM.getResult<CallGraphAnalysis>(M);
  return TypeGraphPassInternal(M,CG).run() ? PreservedAnalyses::none() : PreservedAnalyses::all();
}

bool TypeGraphLegacyPass::runOnModule(Module &M) {
   CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
   return TypeGraphPassInternal(M,CG).run(); }


char TypeGraphLegacyPass::ID = 0;

TypeGraphLegacyPass::TypeGraphLegacyPass() : ModulePass(ID) {}

void TypeGraphLegacyPass::getAnalysisUsage(AnalysisUsage &AU) const{
    AU.addRequired<CallGraphWrapperPass>();
    // If you do not modify the IR, you can also add:
    AU.setPreservesAll();
}

static RegisterPass<TypeGraphLegacyPass> Registration("TypeGraph", "TypeGraphLegacyPass", false, false);

} // namespace llvm
