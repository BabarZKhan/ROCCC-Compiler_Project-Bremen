// The ROCCC Compiler Infrastructure
//  this file is distributed under the University of California Open Source
//  License.  See ROCCCLICENSE.TXT for details.

#include <cassert>

#include <basicnodes/basic_factory.h>

#include "roccc_utils/warning_utils.h"
#include "roccc_utils/roccc2.0_utils.h"

#include "lutDetectionPass.h"

LUTDetectionPass::LUTDetectionPass(SuifEnv* pEnv)
    : PipelinablePass(pEnv, "LookupTableIdentification"), theEnv(pEnv), procDef(nullptr) {}

void LUTDetectionPass::do_procedure_definition(ProcedureDefinition* p) {
    procDef = p;
    assert(procDef != nullptr && "ProcedureDefinition cannot be null.");

    OutputInformation("LUT Detection Pass begins");

    // LUTs are only valid in New Style Systems or Modules
    if (isLegacy(procDef)) {
        OutputInformation("Legacy code - No LUTs supported");
        return;
    }

    // LUTs are arrays that are not parameter symbols
    SymbolTable* symTab = procDef->get_symbol_table();
    assert(symTab != nullptr && "SymbolTable cannot be null.");

    for (auto* currentObject : symTab->get_objects()) { // Using a range-based loop
        auto* currentVar = dynamic_cast<VariableSymbol*>(currentObject);
        auto* currentParam = dynamic_cast<ParameterSymbol*>(currentObject);

        if (currentVar != nullptr &&
            dynamic_cast<ArrayType*>(currentVar->get_type()->get_base_type()) != nullptr &&
            currentParam == nullptr &&
            currentVar->lookup_annote_by_name("ConstPropArray") == nullptr) {
            
            // Mark the variable as a LUT
            currentObject->append_annote(create_brick_annote(theEnv, "LUT"));
        }
    }

    OutputInformation("LUT Detection Pass ends");
}


