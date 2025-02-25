//===- CodeEmitterGen.cpp - Code Emitter Generator ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// CodeEmitterGen uses the descriptions of instructions and their fields to
// construct an automated code emitter: a function that, given a MachineInstr,
// returns the (currently, 32-bit unsigned) value of the instruction.
//
//===----------------------------------------------------------------------===//

#include "CodeEmitterGen.h"
#include "CodeGenTarget.h"
#include "Record.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

namespace {
const std::unordered_set<std::string> IgnoredInstructions = {
    "PHI", "INLINEASM", "LABEL", "DECLARE", "EXTRACT_SUBREG",
    "INSERT_SUBREG", "IMPLICIT_DEF", "SUBREG_TO_REG"};
}

void CodeEmitterGen::reverseBits(std::vector<Record*> &Insts) {
    for (auto *R : Insts) {
        if (IgnoredInstructions.count(R->getName())) continue;
        
        BitsInit *BI = R->getValueAsBitsInit("Inst");
        unsigned numBits = BI->getNumBits();
        auto *NewBI = new BitsInit(numBits);
        
        for (unsigned bit = 0; bit < numBits / 2; ++bit) {
            unsigned bitSwapIdx = numBits - bit - 1;
            NewBI->setBit(bit, BI->getBit(bitSwapIdx));
            NewBI->setBit(bitSwapIdx, BI->getBit(bit));
        }
        
        if (numBits % 2) {
            unsigned middle = numBits / 2;
            NewBI->setBit(middle, BI->getBit(middle));
        }
        
        R->getValue("Inst")->setValue(NewBI);
    }
}

int CodeEmitterGen::getVariableBit(const std::string &VarName, BitsInit *BI, int bit) {
    if (auto *VBI = dyn_cast<VarBitInit>(BI->getBit(bit))) {
        if (auto *VI = dyn_cast<VarInit>(VBI->getVariable()); VI && VI->getName() == VarName) {
            return VBI->getBitNum();
        }
    }
    return -1;
}

void CodeEmitterGen::run(std::ostream &o) {
    CodeGenTarget Target;
    std::vector<Record*> Insts = Records.getAllDerivedDefinitions("Instruction");
    
    if (Target.isLittleEndianEncoding()) reverseBits(Insts);
    
    EmitSourceFileHeader("Machine Code Emitter", o);
    std::string Namespace = Insts.front()->getValueAsString("Namespace") + "::";
    
    std::vector<const CodeGenInstruction*> NumberedInstructions;
    Target.getInstructionsByEnumValue(NumberedInstructions);
    
    o << "unsigned " << Target.getName() << "CodeEmitter::getBinaryCodeForInstr(MachineInstr &MI) {\n";
    o << "  static const unsigned InstBits[] = {\n";
    
    for (const auto *CGI : NumberedInstructions) {
        Record *R = CGI->TheDef;
        if (IgnoredInstructions.count(R->getName())) {
            o << "    0U,\n";
            continue;
        }
        
        BitsInit *BI = R->getValueAsBitsInit("Inst");
        unsigned Value = 0;
        unsigned e = BI->getNumBits();
        
        for (unsigned i = 0; i < e; ++i) {
            if (auto *B = dyn_cast<BitInit>(BI->getBit(e - i - 1))) {
                Value |= B->getValue() << (e - i - 1);
            }
        }
        
        o << "    " << Value << "U,\n";
    }
    o << "  };\n";
    
    o << "  const unsigned opcode = MI.getOpcode();\n"
      << "  unsigned Value = InstBits[opcode];\n"
      << "  unsigned op;\n"
      << "  switch (opcode) {\n";
    
    std::map<std::string, std::vector<std::string>> CaseMap;
    
    for (auto *R : Insts) {
        const std::string &InstName = R->getName();
        if (IgnoredInstructions.count(InstName)) continue;
        
        BitsInit *BI = R->getValueAsBitsInit("Inst");
        CodeGenInstruction &CGI = Target.getInstruction(InstName);
        
        std::string Case;
        unsigned op = 0;
        
        for (const auto &Val : R->getValues()) {
            const std::string &VarName = Val.getName();
            bool gotOp = false;
            
            for (int bit = BI->getNumBits() - 1; bit >= 0;) {
                int varBit = getVariableBit(VarName, BI, bit);
                if (varBit == -1) { --bit; continue; }
                
                int beginInstBit = bit;
                int beginVarBit = varBit;
                int N = 1;
                
                for (--bit; bit >= 0; --bit) {
                    varBit = getVariableBit(VarName, BI, bit);
                    if (varBit == -1 || varBit != (beginVarBit - N)) break;
                    ++N;
                }
                
                if (!gotOp) {
                    while (CGI.isFlatOperandNotEmitted(op)) ++op;
                    Case += "      op = getMachineOpValue(MI, MI.getOperand(" + utostr(op++) + "));");
                    gotOp = true;
                }
                
                unsigned opMask = (1U << N) - 1;
                int opShift = beginVarBit - N + 1;
                opMask <<= opShift;
                opShift = beginInstBit - beginVarBit;
                
                if (opShift > 0) {
                    Case += "      Value |= (op & " + utostr(opMask) + "U) << " + itostr(opShift) + ";\n";
                } else if (opShift < 0) {
                    Case += "      Value |= (op & " + utostr(opMask) + "U) >> " + itostr(-opShift) + ";\n";
                } else {
                    Case += "      Value |= op & " + utostr(opMask) + "U;\n";
                }
            }
        }
        CaseMap[Case].push_back(InstName);
    }
    
    for (const auto &[Case, InstList] : CaseMap) {
        for (const auto &Inst : InstList) {
            o << "    case " << Namespace << Inst << ":\n";
        }
        o << "    {\n" << Case << "      break;\n    }\n";
    }
    
    o << "  default:\n    llvm::errs() << \"Not supported instr: \" << MI << "\n";
    o << "    abort();\n  }\n  return Value;\n}";
}
