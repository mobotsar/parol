// This file was generated by [ts-rs](https://github.com/Aleph-Alpha/ts-rs). Do not edit this file manually.
import type { ScopeId } from "./ScopeId";
import type { SymbolAttribute } from "./SymbolAttribute";
import type { SymbolId } from "./SymbolId";

export interface Instance { scope: ScopeId, type_id: SymbolId, used: boolean, sem: SymbolAttribute, description: string, }