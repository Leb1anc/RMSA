//== MemRegion.h - Abstract memory regions for static analysis --*- C++ -*--==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file defines MemRegion and its subclasses.  MemRegion defines a
//  partially-typed abstraction of memory useful for path-sensitive dataflow
//  analyses.
//
//===----------------------------------------------------------------------===//

#ifndef Test
#define Test
#endif

#include "clang/AST/DeclBase.h"
#include "clang/AST/DeclarationName.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Type.h"
#include "clang/Sema/Ownership.h"
#include "llvm/ADT/APInt.h"
#include <cstdio>
#ifndef LLVM_CLANG_STATICANALYZER_CORE_PATHSENSITIVE_MEMREGION_H
#define LLVM_CLANG_STATICANALYZER_CORE_PATHSENSITIVE_MEMREGION_H

#include "clang/AST/ASTContext.h"
#include "clang/AST/CharUnits.h"
#include "clang/AST/Decl.h"
#include "clang/AST/ExprObjC.h"
#include "clang/Basic/LLVM.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.h"
#include "llvm/ADT/FoldingSet.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/ErrorHandling.h"
#include <string>

namespace clang {

class LocationContext;
class StackFrameContext;

namespace ento {

class CodeTextRegion;
class MemRegionManager;
class MemSpaceRegion;
class SValBuilder;
class SymbolicRegion;
class VarRegion;

/// Represent a region's offset within the top level base region.
class RegionOffset {
  /// The base region.
  const MemRegion *R;

  /// The bit offset within the base region. It shouldn't be negative.
  int64_t Offset;

public:
  // We're using a const instead of an enumeration due to the size required;
  // Visual Studio will only create enumerations of size int, not long long.
  static const int64_t Symbolic = INT64_MAX;

  RegionOffset() : R(nullptr) {}
  RegionOffset(const MemRegion *r, int64_t off) : R(r), Offset(off) {}

  const MemRegion *getRegion() const { return R; }

  bool hasSymbolicOffset() const { return Offset == Symbolic; }

  int64_t getOffset() const {
    assert(!hasSymbolicOffset());
    return Offset;
  }

  bool isValid() const { return R; }
};

//===----------------------------------------------------------------------===//
// Base region classes.
//===----------------------------------------------------------------------===//

/// MemRegion - The root abstract class for all memory regions.
class MemRegion : public llvm::FoldingSetNode {
  friend class MemRegionManager;

public:
  enum Kind {
    // Memory spaces.
    GenericMemSpaceRegionKind,
    StackLocalsSpaceRegionKind,
    StackArgumentsSpaceRegionKind,
    HeapSpaceRegionKind,
    UnknownSpaceRegionKind,
    StaticGlobalSpaceRegionKind,
    GlobalInternalSpaceRegionKind,
    GlobalSystemSpaceRegionKind,
    GlobalImmutableSpaceRegionKind,
    BEG_NON_STATIC_GLOBAL_MEMSPACES = GlobalInternalSpaceRegionKind,
    END_NON_STATIC_GLOBAL_MEMSPACES = GlobalImmutableSpaceRegionKind,
    BEG_GLOBAL_MEMSPACES = StaticGlobalSpaceRegionKind,
    END_GLOBAL_MEMSPACES = GlobalImmutableSpaceRegionKind,
    BEG_MEMSPACES = GenericMemSpaceRegionKind,
    END_MEMSPACES = GlobalImmutableSpaceRegionKind,
    // Untyped regions.
    SymbolicRegionKind,
    AllocaRegionKind,
    // Typed regions.
    BEG_TYPED_REGIONS,
    FunctionTextRegionKind = BEG_TYPED_REGIONS,
    BlockTextRegionKind,
    BlockDataRegionKind,
    BEG_TYPED_VALUE_REGIONS,
    CompoundLiteralRegionKind = BEG_TYPED_VALUE_REGIONS,
    CXXThisRegionKind,
    StringRegionKind,
    ObjCStringRegionKind,
    ElementRegionKind,
    // Decl Regions.
    BEG_DECL_REGIONS,
    VarRegionKind = BEG_DECL_REGIONS,
    FieldRegionKind,
    ObjCIvarRegionKind,
    END_DECL_REGIONS = ObjCIvarRegionKind,
    CXXTempObjectRegionKind,
    CXXBaseObjectRegionKind,
    END_TYPED_VALUE_REGIONS = CXXBaseObjectRegionKind,
    END_TYPED_REGIONS = CXXBaseObjectRegionKind
  };

private:
  const Kind kind;

protected:
  MemRegion(Kind k) : kind(k) {}
  virtual ~MemRegion();

public:
  ASTContext &getContext() const;

  virtual void Profile(llvm::FoldingSetNodeID &ID) const = 0;

  virtual MemRegionManager *getMemRegionManager() const = 0;

  const MemSpaceRegion *getMemorySpace() const;

  const MemRegion *getBaseRegion() const;

  /// Check if the region is a subregion of the given region.
  virtual bool isSubRegionOf(const MemRegion *R) const;

  const MemRegion *StripCasts(bool StripBaseCasts = true) const;

  /// \brief If this is a symbolic region, returns the region. Otherwise,
  /// goes up the base chain looking for the first symbolic base region.
  const SymbolicRegion *getSymbolicBase() const;

  bool hasGlobalsOrParametersStorage() const;

  bool hasStackStorage() const;

  bool hasStackNonParametersStorage() const;

  bool hasStackParametersStorage() const;

  /// Compute the offset within the top level memory object.
  RegionOffset getAsOffset() const;

  /// \brief Get a string representation of a region for debug use.
  std::string getString() const;

  virtual void dumpToStream(raw_ostream &os) const;

  void dump() const;

  /// \brief Returns true if this region can be printed in a user-friendly way.
  virtual bool canPrintPretty() const;

  /// \brief Print the region for use in diagnostics.
  virtual void printPretty(raw_ostream &os) const;

  /// \brief Returns true if this region's textual representation can be used
  /// as part of a larger expression.
  virtual bool canPrintPrettyAsExpr() const;

  /// \brief Print the region as expression.
  ///
  /// When this region represents a subexpression, the method is for printing
  /// an expression containing it.
  virtual void printPrettyAsExpr(raw_ostream &os) const;

  Kind getKind() const { return kind; }

  template <typename RegionTy> const RegionTy *getAs() const;

  virtual bool isBoundable() const { return false; }
};

/// MemSpaceRegion - A memory region that represents a "memory space";
///  for example, the set of global variables, the stack frame, etc.
class MemSpaceRegion : public MemRegion {
protected:
  friend class MemRegionManager;

  MemRegionManager *Mgr;

  MemSpaceRegion(MemRegionManager *mgr, Kind k = GenericMemSpaceRegionKind)
      : MemRegion(k), Mgr(mgr) {
    assert(classof(this));
  }

  MemRegionManager *getMemRegionManager() const override { return Mgr; }

public:
  bool isBoundable() const override { return false; }

  void Profile(llvm::FoldingSetNodeID &ID) const override;

  static bool classof(const MemRegion *R) {
    Kind k = R->getKind();
    return k >= BEG_MEMSPACES && k <= END_MEMSPACES;
  }
};

class GlobalsSpaceRegion : public MemSpaceRegion {
  virtual void anchor();

protected:
  GlobalsSpaceRegion(MemRegionManager *mgr, Kind k) : MemSpaceRegion(mgr, k) {}

public:
  static bool classof(const MemRegion *R) {
    Kind k = R->getKind();
    return k >= BEG_GLOBAL_MEMSPACES && k <= END_GLOBAL_MEMSPACES;
  }
};

/// \brief The region of the static variables within the current CodeTextRegion
/// scope.
///
/// Currently, only the static locals are placed there, so we know that these
/// variables do not get invalidated by calls to other functions.
class StaticGlobalSpaceRegion : public GlobalsSpaceRegion {
  friend class MemRegionManager;

  const CodeTextRegion *CR;

  StaticGlobalSpaceRegion(MemRegionManager *mgr, const CodeTextRegion *cr)
      : GlobalsSpaceRegion(mgr, StaticGlobalSpaceRegionKind), CR(cr) {}

public:
  void Profile(llvm::FoldingSetNodeID &ID) const override;

  void dumpToStream(raw_ostream &os) const override;

  const CodeTextRegion *getCodeRegion() const { return CR; }

  static bool classof(const MemRegion *R) {
    return R->getKind() == StaticGlobalSpaceRegionKind;
  }
};

/// \brief The region for all the non-static global variables.
///
/// This class is further split into subclasses for efficient implementation of
/// invalidating a set of related global values as is done in
/// RegionStoreManager::invalidateRegions (instead of finding all the dependent
/// globals, we invalidate the whole parent region).
class NonStaticGlobalSpaceRegion : public GlobalsSpaceRegion {
  friend class MemRegionManager;

protected:
  NonStaticGlobalSpaceRegion(MemRegionManager *mgr, Kind k)
      : GlobalsSpaceRegion(mgr, k) {}

public:
  static bool classof(const MemRegion *R) {
    Kind k = R->getKind();
    return k >= BEG_NON_STATIC_GLOBAL_MEMSPACES &&
           k <= END_NON_STATIC_GLOBAL_MEMSPACES;
  }
};

/// \brief The region containing globals which are defined in system/external
/// headers and are considered modifiable by system calls (ex: errno).
class GlobalSystemSpaceRegion : public NonStaticGlobalSpaceRegion {
  friend class MemRegionManager;

  GlobalSystemSpaceRegion(MemRegionManager *mgr)
      : NonStaticGlobalSpaceRegion(mgr, GlobalSystemSpaceRegionKind) {}

public:
  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == GlobalSystemSpaceRegionKind;
  }
};

/// \brief The region containing globals which are considered not to be modified
/// or point to data which could be modified as a result of a function call
/// (system or internal). Ex: Const global scalars would be modeled as part of
/// this region. This region also includes most system globals since they have
/// low chance of being modified.
class GlobalImmutableSpaceRegion : public NonStaticGlobalSpaceRegion {
  friend class MemRegionManager;

  GlobalImmutableSpaceRegion(MemRegionManager *mgr)
      : NonStaticGlobalSpaceRegion(mgr, GlobalImmutableSpaceRegionKind) {}

public:
  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == GlobalImmutableSpaceRegionKind;
  }
};

/// \brief The region containing globals which can be modified by calls to
/// "internally" defined functions - (for now just) functions other then system
/// calls.
class GlobalInternalSpaceRegion : public NonStaticGlobalSpaceRegion {
  friend class MemRegionManager;

  GlobalInternalSpaceRegion(MemRegionManager *mgr)
      : NonStaticGlobalSpaceRegion(mgr, GlobalInternalSpaceRegionKind) {}

public:
  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == GlobalInternalSpaceRegionKind;
  }
};

class HeapSpaceRegion : public MemSpaceRegion {
  virtual void anchor();
  friend class MemRegionManager;

  HeapSpaceRegion(MemRegionManager *mgr)
      : MemSpaceRegion(mgr, HeapSpaceRegionKind) {}

public:
  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == HeapSpaceRegionKind;
  }
};

class UnknownSpaceRegion : public MemSpaceRegion {
  virtual void anchor();
  friend class MemRegionManager;
  UnknownSpaceRegion(MemRegionManager *mgr)
      : MemSpaceRegion(mgr, UnknownSpaceRegionKind) {}

public:
  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == UnknownSpaceRegionKind;
  }
};

class StackSpaceRegion : public MemSpaceRegion {
private:
  const StackFrameContext *SFC;

protected:
  StackSpaceRegion(MemRegionManager *mgr, Kind k, const StackFrameContext *sfc)
      : MemSpaceRegion(mgr, k), SFC(sfc) {
    assert(classof(this));
  }

public:
  const StackFrameContext *getStackFrame() const { return SFC; }

  void Profile(llvm::FoldingSetNodeID &ID) const override;

  static bool classof(const MemRegion *R) {
    Kind k = R->getKind();
    return k >= StackLocalsSpaceRegionKind &&
           k <= StackArgumentsSpaceRegionKind;
  }
};

class StackLocalsSpaceRegion : public StackSpaceRegion {
  virtual void anchor();
  friend class MemRegionManager;
  StackLocalsSpaceRegion(MemRegionManager *mgr, const StackFrameContext *sfc)
      : StackSpaceRegion(mgr, StackLocalsSpaceRegionKind, sfc) {}

public:
  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == StackLocalsSpaceRegionKind;
  }
};

class StackArgumentsSpaceRegion : public StackSpaceRegion {
private:
  virtual void anchor();
  friend class MemRegionManager;
  StackArgumentsSpaceRegion(MemRegionManager *mgr, const StackFrameContext *sfc)
      : StackSpaceRegion(mgr, StackArgumentsSpaceRegionKind, sfc) {}

public:
  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == StackArgumentsSpaceRegionKind;
  }
};

/// SubRegion - A region that subsets another larger region.  Most regions
///  are subclasses of SubRegion.
class SubRegion : public MemRegion {
private:
  virtual void anchor();

protected:
  const MemRegion *superRegion;
  SubRegion(const MemRegion *sReg, Kind k) : MemRegion(k), superRegion(sReg) {}

public:
  const MemRegion *getSuperRegion() const { return superRegion; }

  /// getExtent - Returns the size of the region in bytes.
  virtual DefinedOrUnknownSVal getExtent(SValBuilder &svalBuilder) const {
    return UnknownVal();
  }

  MemRegionManager *getMemRegionManager() const override;

  bool isSubRegionOf(const MemRegion *R) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() > END_MEMSPACES;
  }
};

//===----------------------------------------------------------------------===//
// MemRegion subclasses.
//===----------------------------------------------------------------------===//

/// AllocaRegion - A region that represents an untyped blob of bytes created
///  by a call to 'alloca'.
class AllocaRegion : public SubRegion {
  friend class MemRegionManager;

protected:
  unsigned Cnt; // Block counter.  Used to distinguish different pieces of
                // memory allocated by alloca at the same call site.
  const Expr *Ex;

  AllocaRegion(const Expr *ex, unsigned cnt, const MemRegion *superRegion)
      : SubRegion(superRegion, AllocaRegionKind), Cnt(cnt), Ex(ex) {}

public:
  const Expr *getExpr() const { return Ex; }

  bool isBoundable() const override { return true; }

  DefinedOrUnknownSVal getExtent(SValBuilder &svalBuilder) const override;

  void Profile(llvm::FoldingSetNodeID &ID) const override;

  static void ProfileRegion(llvm::FoldingSetNodeID &ID, const Expr *Ex,
                            unsigned Cnt, const MemRegion *superRegion);

  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == AllocaRegionKind;
  }
};

/// TypedRegion - An abstract class representing regions that are typed.
class TypedRegion : public SubRegion {
public:
  void anchor() override;

protected:
  TypedRegion(const MemRegion *sReg, Kind k) : SubRegion(sReg, k) {}

public:
  virtual QualType getLocationType() const = 0;

  QualType getDesugaredLocationType(ASTContext &Context) const {
    return getLocationType().getDesugaredType(Context);
  }

  bool isBoundable() const override { return true; }

  static bool classof(const MemRegion *R) {
    unsigned k = R->getKind();
    return k >= BEG_TYPED_REGIONS && k <= END_TYPED_REGIONS;
  }
};

/// TypedValueRegion - An abstract class representing regions having a typed
/// value.
class TypedValueRegion : public TypedRegion {
public:
  void anchor() override;

protected:
  TypedValueRegion(const MemRegion *sReg, Kind k) : TypedRegion(sReg, k) {}

public:
  virtual QualType getValueType() const = 0;

  QualType getLocationType() const override {
    // FIXME: We can possibly optimize this later to cache this value.
    QualType T = getValueType();
    ASTContext &ctx = getContext();
    if (T->getAs<ObjCObjectType>())
      return ctx.getObjCObjectPointerType(T);
    return ctx.getPointerType(getValueType());
  }

  QualType getDesugaredValueType(ASTContext &Context) const {
    QualType T = getValueType();
    return T.getTypePtrOrNull() ? T.getDesugaredType(Context) : T;
  }

  DefinedOrUnknownSVal getExtent(SValBuilder &svalBuilder) const override;

  static bool classof(const MemRegion *R) {
    unsigned k = R->getKind();
    return k >= BEG_TYPED_VALUE_REGIONS && k <= END_TYPED_VALUE_REGIONS;
  }
};

class CodeTextRegion : public TypedRegion {
public:
  void anchor() override;

protected:
  CodeTextRegion(const MemRegion *sreg, Kind k) : TypedRegion(sreg, k) {}

public:
  bool isBoundable() const override { return false; }

  static bool classof(const MemRegion *R) {
    Kind k = R->getKind();
    return k >= FunctionTextRegionKind && k <= BlockTextRegionKind;
  }
};

/// FunctionTextRegion - A region that represents code texts of function.
class FunctionTextRegion : public CodeTextRegion {
  const NamedDecl *FD;

public:
  FunctionTextRegion(const NamedDecl *fd, const MemRegion *sreg)
      : CodeTextRegion(sreg, FunctionTextRegionKind), FD(fd) {
    assert(isa<ObjCMethodDecl>(fd) || isa<FunctionDecl>(fd));
  }

  QualType getLocationType() const override {
    const ASTContext &Ctx = getContext();
    if (const FunctionDecl *D = dyn_cast<FunctionDecl>(FD)) {
      return Ctx.getPointerType(D->getType());
    }

    assert(isa<ObjCMethodDecl>(FD));
    assert(false && "Getting the type of ObjCMethod is not supported yet");

    // TODO: We might want to return a different type here (ex: id (*ty)(...))
    //       depending on how it is used.
    return QualType();
  }

  const NamedDecl *getDecl() const { return FD; }

  void dumpToStream(raw_ostream &os) const override;

  void Profile(llvm::FoldingSetNodeID &ID) const override;

  static void ProfileRegion(llvm::FoldingSetNodeID &ID, const NamedDecl *FD,
                            const MemRegion *);

  static bool classof(const MemRegion *R) {
    return R->getKind() == FunctionTextRegionKind;
  }
};

/// BlockTextRegion - A region that represents code texts of blocks (closures).
///  Blocks are represented with two kinds of regions.  BlockTextRegions
///  represent the "code", while BlockDataRegions represent instances of blocks,
///  which correspond to "code+data".  The distinction is important, because
///  like a closure a block captures the values of externally referenced
///  variables.
class BlockTextRegion : public CodeTextRegion {
  friend class MemRegionManager;

  const BlockDecl *BD;
  AnalysisDeclContext *AC;
  CanQualType locTy;

  BlockTextRegion(const BlockDecl *bd, CanQualType lTy, AnalysisDeclContext *ac,
                  const MemRegion *sreg)
      : CodeTextRegion(sreg, BlockTextRegionKind), BD(bd), AC(ac), locTy(lTy) {}

public:
  QualType getLocationType() const override { return locTy; }

  const BlockDecl *getDecl() const { return BD; }

  AnalysisDeclContext *getAnalysisDeclContext() const { return AC; }

  virtual void dumpToStream(raw_ostream &os) const override;

  void Profile(llvm::FoldingSetNodeID &ID) const override;

  static void ProfileRegion(llvm::FoldingSetNodeID &ID, const BlockDecl *BD,
                            CanQualType, const AnalysisDeclContext *,
                            const MemRegion *);

  static bool classof(const MemRegion *R) {
    return R->getKind() == BlockTextRegionKind;
  }
};

/// BlockDataRegion - A region that represents a block instance.
///  Blocks are represented with two kinds of regions.  BlockTextRegions
///  represent the "code", while BlockDataRegions represent instances of blocks,
///  which correspond to "code+data".  The distinction is important, because
///  like a closure a block captures the values of externally referenced
///  variables.
class BlockDataRegion : public TypedRegion {
  friend class MemRegionManager;
  const BlockTextRegion *BC;
  const LocationContext *LC; // Can be null */
  unsigned BlockCount;
  void *ReferencedVars;
  void *OriginalVars;

  BlockDataRegion(const BlockTextRegion *bc, const LocationContext *lc,
                  unsigned count, const MemRegion *sreg)
      : TypedRegion(sreg, BlockDataRegionKind), BC(bc), LC(lc),
        BlockCount(count), ReferencedVars(nullptr), OriginalVars(nullptr) {}

public:
  const BlockTextRegion *getCodeRegion() const { return BC; }

  const BlockDecl *getDecl() const { return BC->getDecl(); }

  QualType getLocationType() const override { return BC->getLocationType(); }

  class referenced_vars_iterator {
    const MemRegion *const *R;
    const MemRegion *const *OriginalR;

  public:
    explicit referenced_vars_iterator(const MemRegion *const *r,
                                      const MemRegion *const *originalR)
        : R(r), OriginalR(originalR) {}

    const VarRegion *getCapturedRegion() const { return cast<VarRegion>(*R); }
    const VarRegion *getOriginalRegion() const {
      return cast<VarRegion>(*OriginalR);
    }

    bool operator==(const referenced_vars_iterator &I) const {
      assert((R == nullptr) == (I.R == nullptr));
      return I.R == R;
    }
    bool operator!=(const referenced_vars_iterator &I) const {
      assert((R == nullptr) == (I.R == nullptr));
      return I.R != R;
    }
    referenced_vars_iterator &operator++() {
      ++R;
      ++OriginalR;
      return *this;
    }
  };

  /// Return the original region for a captured region, if
  /// one exists.
  const VarRegion *getOriginalRegion(const VarRegion *VR) const;

  referenced_vars_iterator referenced_vars_begin() const;
  referenced_vars_iterator referenced_vars_end() const;

  void dumpToStream(raw_ostream &os) const override;

  void Profile(llvm::FoldingSetNodeID &ID) const override;

  static void ProfileRegion(llvm::FoldingSetNodeID &, const BlockTextRegion *,
                            const LocationContext *, unsigned,
                            const MemRegion *);

  static bool classof(const MemRegion *R) {
    return R->getKind() == BlockDataRegionKind;
  }

private:
  void LazyInitializeReferencedVars();
  std::pair<const VarRegion *, const VarRegion *>
  getCaptureRegions(const VarDecl *VD);
};

/// SymbolicRegion - A special, "non-concrete" region. Unlike other region
///  clases, SymbolicRegion represents a region that serves as an alias for
///  either a real region, a NULL pointer, etc.  It essentially is used to
///  map the concept of symbolic values into the domain of regions.  Symbolic
///  regions do not need to be typed.
class SymbolicRegion : public SubRegion {

#ifdef Test
public:
  class MallocRegion;

private:
  MallocRegion *mallocRegion = nullptr;
  bool _isHeap = false;

#endif

protected:
  const SymbolRef sym;

public:
  SymbolicRegion(const SymbolRef s, const MemRegion *sreg)
      : SubRegion(sreg, SymbolicRegionKind), sym(s) {}

  SymbolRef getSymbol() const { return sym; }

  bool isBoundable() const override { return true; }

  DefinedOrUnknownSVal getExtent(SValBuilder &svalBuilder) const override;

  void Profile(llvm::FoldingSetNodeID &ID) const override;

  static void ProfileRegion(llvm::FoldingSetNodeID &ID, SymbolRef sym,
                            const MemRegion *superRegion);

  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == SymbolicRegionKind;
  }
#ifdef Test
  ~SymbolicRegion() {
    if (!mallocRegion)
      delete mallocRegion;
  }
#endif

#ifdef Test
  // 如果当前堆区域属于C语言堆内存区域，则使用该类描述该堆内存的相关信息
  class MallocRegion {

  public:
    enum HeapState { allocted, freed, leaked, unknowned, escaped };

  private:
    HeapState state;
    int count;
    const int ByteLength;

  public:
    MallocRegion(int _byteLength)
        : state(allocted), count(1), ByteLength(_byteLength) {}

    HeapState getHeapState() { return state; }
    void setHeapState(HeapState _state) { state = _state; }

    int getCount() { return count; }
    void addCount() { count++; }
    void subCount() { count--; }

    int getLength() { return ByteLength; }
  };

  bool isHeap() { return _isHeap; }
  void createMallocRegion(int byteLength) {
    _isHeap = true;
    mallocRegion = new MallocRegion(byteLength);
  }
  MallocRegion *getMallocRegion() { return mallocRegion; }

#endif
};

/// StringRegion - Region associated with a StringLiteral.
class StringRegion : public TypedValueRegion {
  friend class MemRegionManager;
  const StringLiteral *Str;

protected:
  StringRegion(const StringLiteral *str, const MemRegion *sreg)
      : TypedValueRegion(sreg, StringRegionKind), Str(str) {}

  static void ProfileRegion(llvm::FoldingSetNodeID &ID,
                            const StringLiteral *Str,
                            const MemRegion *superRegion);

public:
  const StringLiteral *getStringLiteral() const { return Str; }

  QualType getValueType() const override { return Str->getType(); }

  DefinedOrUnknownSVal getExtent(SValBuilder &svalBuilder) const override;

  bool isBoundable() const override { return false; }

  void Profile(llvm::FoldingSetNodeID &ID) const override {
    ProfileRegion(ID, Str, superRegion);
  }

  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == StringRegionKind;
  }
};

/// The region associated with an ObjCStringLiteral.
class ObjCStringRegion : public TypedValueRegion {
  friend class MemRegionManager;
  const ObjCStringLiteral *Str;

protected:
  ObjCStringRegion(const ObjCStringLiteral *str, const MemRegion *sreg)
      : TypedValueRegion(sreg, ObjCStringRegionKind), Str(str) {}

  static void ProfileRegion(llvm::FoldingSetNodeID &ID,
                            const ObjCStringLiteral *Str,
                            const MemRegion *superRegion);

public:
  const ObjCStringLiteral *getObjCStringLiteral() const { return Str; }

  QualType getValueType() const override { return Str->getType(); }

  bool isBoundable() const override { return false; }

  void Profile(llvm::FoldingSetNodeID &ID) const override {
    ProfileRegion(ID, Str, superRegion);
  }

  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == ObjCStringRegionKind;
  }
};

/// CompoundLiteralRegion - A memory region representing a compound literal.
///   Compound literals are essentially temporaries that are stack allocated
///   or in the global constant pool.
class CompoundLiteralRegion : public TypedValueRegion {
private:
  friend class MemRegionManager;
  const CompoundLiteralExpr *CL;

  CompoundLiteralRegion(const CompoundLiteralExpr *cl, const MemRegion *sReg)
      : TypedValueRegion(sReg, CompoundLiteralRegionKind), CL(cl) {}

  static void ProfileRegion(llvm::FoldingSetNodeID &ID,
                            const CompoundLiteralExpr *CL,
                            const MemRegion *superRegion);

public:
  QualType getValueType() const override { return CL->getType(); }

  bool isBoundable() const override { return !CL->isFileScope(); }

  void Profile(llvm::FoldingSetNodeID &ID) const override;

  void dumpToStream(raw_ostream &os) const override;

  const CompoundLiteralExpr *getLiteralExpr() const { return CL; }

  static bool classof(const MemRegion *R) {
    return R->getKind() == CompoundLiteralRegionKind;
  }
};

class DeclRegion : public TypedValueRegion {
protected:
  const Decl *D;

  DeclRegion(const Decl *d, const MemRegion *sReg, Kind k)
      : TypedValueRegion(sReg, k), D(d) {}

  static void ProfileRegion(llvm::FoldingSetNodeID &ID, const Decl *D,
                            const MemRegion *superRegion, Kind k);

public:
  const Decl *getDecl() const { return D; }
  void Profile(llvm::FoldingSetNodeID &ID) const override;

  static bool classof(const MemRegion *R) {
    unsigned k = R->getKind();
    return k >= BEG_DECL_REGIONS && k <= END_DECL_REGIONS;
  }
};

//定义几类VarRegion
#ifdef Test

//基类
class VarBase {
public:
  enum RegionType {
    builtinType,
    ptrType,
    arrayType,
    structType,
    unionType,
    enumType
  };

private:
  RegionType regionType;

public:
  VarBase(RegionType k) : regionType(k) {}

  RegionType getRegionType() { return regionType; }
};

//基本数据类型所属的区域类型，例如int、float等，主要保存该变量类型信息
class BuiltinRegion : public VarBase {

  VarRegion *absRegion;
  const VarDecl *varDecl;
  BuiltinType::Kind varType;

public:
  BuiltinRegion(VarRegion *_absRegion, const VarDecl *_varDecl)
      : VarBase(builtinType), absRegion(_absRegion), varDecl(_varDecl) {
    if (const BuiltinType *BT =
            dyn_cast<BuiltinType>(varDecl->getType()
                                      ->getUnqualifiedDesugaredType()
                                      ->getCanonicalTypeInternal()))
      varType = BT->getKind();
    else
      fprintf(stderr, "该变量%s的 pureKind not in Kind",
              varDecl->getNameAsString().c_str());
  }

  VarRegion *getVarRegion() { return absRegion; }
  const VarDecl *getDecl() { return varDecl; }
  BuiltinType::Kind getvarType() { return varType; }

  static bool isBuiltin(VarBase *varRegion) {
    return varRegion->getRegionType() == RegionType::builtinType;
  }
};

class EnumRegion : public VarBase {

  VarRegion *absRegion;
  const VarDecl *varDecl;

public:
  EnumRegion(VarRegion *_absRegion, const VarDecl *_varDecl)
      : VarBase(builtinType), absRegion(_absRegion), varDecl(_varDecl) {
    if (!varDecl->getType()->getUnqualifiedDesugaredType()->isEnumeralType())
      fprintf(stderr, "该变量%s的 pureKind is not EnumType",
              varDecl->getNameAsString().c_str());
  }

  VarRegion *getVarRegion() { return absRegion; }
  const VarDecl *getDecl() { return varDecl; }

  static bool isEnum(VarBase *varRegion) {
    return varRegion->getRegionType() == RegionType::enumType;
  }
};

//指针类型变量所属的区域类型，除了保存指针类型外，记录当前指针在分析期间的状态。
class PtrRegion : public VarBase {

  //指向的数据类型
  enum Kind { Builtin, Array, Struct, Union, Enum, Function };

  //指针状态
  enum PtrState { null, toHeap, toStack, toGlobal, wild, dangling, toUnknown };

  VarRegion *absRegion;
  const VarDecl *varDecl;
  QualType ptreeType;
  QualType pureType;
  Kind pureKind;
  PtrState state;

public:
  PtrRegion(VarRegion *_absRegion, const VarDecl *_varDecl)
      : VarBase(ptrType), absRegion(_absRegion), varDecl(_varDecl) {
    assert(isa<PointerType>(varDecl->getType()));

    //获得该指针指向什么类型
    ptreeType =
        varDecl->getType()->getUnqualifiedDesugaredType()->getPointeeType();

    //判断该指针指向什么数据类型
    QualType tempType = ptreeType;
    while (isa<PointerType>(tempType.getCanonicalType())) {
      tempType = tempType->getPointeeType();
    }
    pureType = tempType;
    const BuiltinType *BT;
    if ((BT = dyn_cast<BuiltinType>(pureType->getCanonicalTypeInternal())))
      pureKind = Kind::Builtin;
    else if (isa<ArrayType>(pureType->getCanonicalTypeInternal()))
      pureKind = Kind::Array;
    else if (pureType->getAs<RecordType>()->getDecl()->isStruct())
      pureKind = Kind::Struct;
    else if (pureType->getAs<RecordType>()->getDecl()->isUnion())
      pureKind = Kind::Union;
    else if (isa<FunctionType>(pureType->getCanonicalTypeInternal()))
      pureKind = Kind::Function;
    else {
      fprintf(stderr, "该变量%s的 pureKind not in Kind",
              varDecl->getNameAsString().c_str());
    }

    //根据指针的初始化方式与内存分区，初始化指针状态
    const Expr *initExpr = varDecl->getInit();

    if (!initExpr) {
      if (varDecl->isLocalVarDecl())
        state = PtrState::wild;
      else
        state = PtrState::null;
    }
  }

  VarRegion *getVarRegion() { return absRegion; }
  const VarDecl *getDecl() { return varDecl; }
  QualType getType() { return varDecl->getType(); }

  QualType getPtreeType() { return ptreeType; }
  QualType getPureType() { return pureType; }
  Kind getPureKind() { return pureKind; }

  PtrState getPtrState() { return state; }
  void setPtrState(PtrState _state) { state = _state; }

  static bool isPtr(VarBase *varRegion) {
    return varRegion->getRegionType() == RegionType::ptrType;
  }
  // void setPtrState(Expr *initExpr, CheckerContext &C);
};

//数组结构区域，记录数组的初始化长度
class ArrayRegion : public VarBase {

  enum Kind { Builtin, Array, Struct, Union, Enum, Function };

  VarRegion *absRegion;
  const VarDecl *varDecl;
  QualType elementType;
  QualType pureType;
  Kind pureKind;
  llvm::APInt len;

public:
  ArrayRegion(VarRegion *_absRegion, const VarDecl *_varDecl)
      : VarBase(arrayType), absRegion(_absRegion), varDecl(_varDecl) {
    const Type *type = varDecl->getType().getTypePtr();
    if (!type->isArrayType()) {
      fprintf(stderr, "该变量%s不是数组类型发生错误",
              varDecl->getNameAsString().c_str());
    }
    if (isa<ConstantArrayType>(type->getCanonicalTypeInternal())) {
      // todo 转换为Int类型
      const ConstantArrayType *CAType =
          dyn_cast<ConstantArrayType>(type->getAsArrayTypeUnsafe());
      if (!CAType) {
        fprintf(stderr, "var: %s dyncast error",
                varDecl->getNameAsString().c_str());
        exit(1);
      }
      len = CAType->getSize();
    }

    while (const ArrayType *arrayType = type->getAsArrayTypeUnsafe()) {
      type = arrayType->getElementType().getTypePtr();
    }
    elementType = type->getCanonicalTypeInternal();
    QualType qualType = elementType;
    while (isa<PointerType>(qualType.getCanonicalType())) {
      qualType = qualType->getPointeeType();
    }
    pureType = qualType;

    if (type->isBuiltinType())
      pureKind = Kind::Builtin;
    else if (pureType->isArrayType())
      pureKind = Kind::Array;
    else if (pureType->isStructureType())
      pureKind = Kind::Struct;
    else if (pureType->isUnionType())
      pureKind = Kind::Union;
    else if (type->isEnumeralType())
      pureKind = Kind::Enum;
    else if (type->isFunctionType())
      pureKind = Kind::Function;
    else {
      fprintf(stderr, "该变量%s的 pureKind not in Kind",
              varDecl->getNameAsString().c_str());
    }
  }

  VarRegion *getVarRegion() { return absRegion; }
  const VarDecl *getDecl() { return varDecl; }
  QualType getElementType() { return elementType; }
  QualType getPureType() { return pureType; }
  Kind getPureKind() { return pureKind; }

  static bool isArrray(VarBase *varRegion) {
    return varRegion->getRegionType() == RegionType::arrayType;
  }
};

//数据结构体区域
class StructRegion : public VarBase {

  VarRegion *absRegion;
  const VarDecl *varDecl;

  RecordDecl *varType;

public:
  StructRegion(VarRegion *_absRegion, const VarDecl *_varDecl)
      : VarBase(structType), absRegion(_absRegion), varDecl(_varDecl) {
    const Type *varType = varDecl->getType()->getUnqualifiedDesugaredType();
    const RecordType *recordType = varType->getAs<RecordType>();
    if (!recordType) {
      fprintf(stderr, "该声明%s不是数据结构类型",
              varDecl->getNameAsString().c_str());
      exit(1);
    }
    this->varType = recordType->getDecl();
  }

  VarRegion *getVarRegion() { return absRegion; }
  const VarDecl *getDecl() { return varDecl; }
  QualType getType() { return varDecl->getType(); }

  static bool isStruct(VarBase *varRegion) {
    return varRegion->getRegionType() == RegionType::structType;
  }
};
#endif

class FieldRegion : public DeclRegion {
  friend class MemRegionManager;

  FieldRegion(const FieldDecl *fd, const MemRegion *sReg)
      : DeclRegion(fd, sReg, FieldRegionKind) {}

public:
  const FieldDecl *getDecl() const { return cast<FieldDecl>(D); }

  QualType getValueType() const override {
    // FIXME: We can cache this if needed.
    return getDecl()->getType();
  }

  DefinedOrUnknownSVal getExtent(SValBuilder &svalBuilder) const override;

  static void ProfileRegion(llvm::FoldingSetNodeID &ID, const FieldDecl *FD,
                            const MemRegion *superRegion) {
    DeclRegion::ProfileRegion(ID, FD, superRegion, FieldRegionKind);
  }

  static bool classof(const MemRegion *R) {
    return R->getKind() == FieldRegionKind;
  }

  void dumpToStream(raw_ostream &os) const override;

  bool canPrintPretty() const override;
  void printPretty(raw_ostream &os) const override;
  bool canPrintPrettyAsExpr() const override;
  void printPrettyAsExpr(raw_ostream &os) const override;
};

class ElementRegion;

//封装了
class RegionRawOffset {
private:
  friend class ElementRegion;

  const MemRegion *Region;
  CharUnits Offset;

  RegionRawOffset(const MemRegion *reg, CharUnits offset = CharUnits::Zero())
      : Region(reg), Offset(offset) {}

public:
  // FIXME: Eventually support symbolic offsets.
  CharUnits getOffset() const { return Offset; }
  const MemRegion *getRegion() const { return Region; }

  void dumpToStream(raw_ostream &os) const;
  void dump() const;
};

/// \brief ElementRegin is used to represent both array elements and casts.
// 元素成员区域，应该设计支持更多连续数据结果对象
class ElementRegion : public TypedValueRegion {
  friend class MemRegionManager;

  QualType ElementType;
  NonLoc Index;

  ElementRegion(QualType elementType, NonLoc Idx, const MemRegion *sReg)
      : TypedValueRegion(sReg, ElementRegionKind), ElementType(elementType),
        Index(Idx) {
    assert((!Idx.getAs<nonloc::ConcreteInt>() ||
            Idx.castAs<nonloc::ConcreteInt>().getValue().isSigned()) &&
           "The index must be signed");
  }

  static void ProfileRegion(llvm::FoldingSetNodeID &ID, QualType elementType,
                            SVal Idx, const MemRegion *superRegion);

public:
  NonLoc getIndex() const { return Index; }

  QualType getValueType() const override { return ElementType; }

  QualType getElementType() const { return ElementType; }
  /// Compute the offset within the array. The array might also be a
  /// subobject.
  RegionRawOffset getAsArrayOffset() const;

  void dumpToStream(raw_ostream &os) const override;

  void Profile(llvm::FoldingSetNodeID &ID) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == ElementRegionKind;
  }
};

//变量类型区域，包含了所有声明形式的变量所存储的区域类型
class VarRegion : public DeclRegion {

  friend class MemRegionManager;

#ifdef Test
  VarBase *varRegion;
#endif

  // Constructors and private methods.
  VarRegion(const VarDecl *vd, const MemRegion *sReg)
      : DeclRegion(vd, sReg, VarRegionKind) {
#ifdef Test
    if (vd->getType()->getUnqualifiedDesugaredType()->isBuiltinType()) {
      varRegion = new BuiltinRegion(this, vd);
    } else if (vd->getType()->getUnqualifiedDesugaredType()->isPointerType()) {
      varRegion = new PtrRegion(this, vd);
    } else if (vd->getType()->getUnqualifiedDesugaredType()->isArrayType()) {
      varRegion = new ArrayRegion(this, vd);
    } else if (vd->getType()
                   ->getUnqualifiedDesugaredType()
                   ->isStructureType()) {
      varRegion = new StructRegion(this, vd);
    } else if (vd->getType()->getUnqualifiedDesugaredType()->isUnionType()) {
      fprintf(stderr, "var is union but will todo");
    } else {
      fprintf(stderr, "%s's type is %s maybe not in Type",
              vd->getNameAsString().c_str(),
              vd->getType()->getUnqualifiedDesugaredType()->getTypeClassName());
    }
#endif
  }

  static void ProfileRegion(llvm::FoldingSetNodeID &ID, const VarDecl *VD,
                            const MemRegion *superRegion) {
    DeclRegion::ProfileRegion(ID, VD, superRegion, VarRegionKind);
  }

  void Profile(llvm::FoldingSetNodeID &ID) const override;

#ifdef Test
  ~VarRegion() { delete varRegion; }
#endif

public:
  const VarDecl *getDecl() const { return cast<VarDecl>(D); }

#ifdef Test
  VarBase *getVarReigon() { return varRegion; }
#endif

  const StackFrameContext *getStackFrame() const;

  QualType getValueType() const override {
    // FIXME: We can cache this if needed.
    return getDecl()->getType();
  }

  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == VarRegionKind;
  }

  bool canPrintPrettyAsExpr() const override;

  void printPrettyAsExpr(raw_ostream &os) const override;
};

/// CXXThisRegion - Represents the region for the implicit 'this' parameter
///  in a call to a C++ method.  This region doesn't represent the object
///  referred to by 'this', but rather 'this' itself.
class CXXThisRegion : public TypedValueRegion {
  friend class MemRegionManager;
  CXXThisRegion(const PointerType *thisPointerTy, const MemRegion *sReg)
      : TypedValueRegion(sReg, CXXThisRegionKind),
        ThisPointerTy(thisPointerTy) {}

  static void ProfileRegion(llvm::FoldingSetNodeID &ID, const PointerType *PT,
                            const MemRegion *sReg);

  void Profile(llvm::FoldingSetNodeID &ID) const override;

public:
  QualType getValueType() const override { return QualType(ThisPointerTy, 0); }

  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == CXXThisRegionKind;
  }

private:
  const PointerType *ThisPointerTy;
};

class ObjCIvarRegion : public DeclRegion {

  friend class MemRegionManager;

  ObjCIvarRegion(const ObjCIvarDecl *ivd, const MemRegion *sReg);

  static void ProfileRegion(llvm::FoldingSetNodeID &ID, const ObjCIvarDecl *ivd,
                            const MemRegion *superRegion);

public:
  const ObjCIvarDecl *getDecl() const;
  QualType getValueType() const override;

  bool canPrintPrettyAsExpr() const override;
  void printPrettyAsExpr(raw_ostream &os) const override;

  void dumpToStream(raw_ostream &os) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == ObjCIvarRegionKind;
  }
};
//===----------------------------------------------------------------------===//
// Auxiliary data classes for use with MemRegions.
//===----------------------------------------------------------------------===//

// C++ temporary object associated with an expression.
class CXXTempObjectRegion : public TypedValueRegion {
  friend class MemRegionManager;

  Expr const *Ex;

  CXXTempObjectRegion(Expr const *E, MemRegion const *sReg)
      : TypedValueRegion(sReg, CXXTempObjectRegionKind), Ex(E) {}

  static void ProfileRegion(llvm::FoldingSetNodeID &ID, Expr const *E,
                            const MemRegion *sReg);

public:
  const Expr *getExpr() const { return Ex; }

  QualType getValueType() const override { return Ex->getType(); }

  void dumpToStream(raw_ostream &os) const override;

  void Profile(llvm::FoldingSetNodeID &ID) const override;

  static bool classof(const MemRegion *R) {
    return R->getKind() == CXXTempObjectRegionKind;
  }
};

// CXXBaseObjectRegion represents a base object within a C++ object. It is
// identified by the base class declaration and the region of its parent
// object.
class CXXBaseObjectRegion : public TypedValueRegion {
  friend class MemRegionManager;

  llvm::PointerIntPair<const CXXRecordDecl *, 1, bool> Data;

  CXXBaseObjectRegion(const CXXRecordDecl *RD, bool IsVirtual,
                      const MemRegion *SReg)
      : TypedValueRegion(SReg, CXXBaseObjectRegionKind), Data(RD, IsVirtual) {}

  static void ProfileRegion(llvm::FoldingSetNodeID &ID, const CXXRecordDecl *RD,
                            bool IsVirtual, const MemRegion *SReg);

public:
  const CXXRecordDecl *getDecl() const { return Data.getPointer(); }
  bool isVirtual() const { return Data.getInt(); }

  QualType getValueType() const override;

  void dumpToStream(raw_ostream &os) const override;

  void Profile(llvm::FoldingSetNodeID &ID) const override;

  static bool classof(const MemRegion *region) {
    return region->getKind() == CXXBaseObjectRegionKind;
  }

  bool canPrintPrettyAsExpr() const override;

  void printPrettyAsExpr(raw_ostream &os) const override;
};

template <typename RegionTy> const RegionTy *MemRegion::getAs() const {
  if (const RegionTy *RT = dyn_cast<RegionTy>(this))
    return RT;

  return nullptr;
}

//===----------------------------------------------------------------------===//
// MemRegionManager - Factory object for creating regions.
//===----------------------------------------------------------------------===//

class MemRegionManager {
  ASTContext &C;
  llvm::BumpPtrAllocator &A;
  llvm::FoldingSet<MemRegion> Regions;

  GlobalInternalSpaceRegion *InternalGlobals;
  GlobalSystemSpaceRegion *SystemGlobals;
  GlobalImmutableSpaceRegion *ImmutableGlobals;

  llvm::DenseMap<const StackFrameContext *, StackLocalsSpaceRegion *>
      StackLocalsSpaceRegions;
  llvm::DenseMap<const StackFrameContext *, StackArgumentsSpaceRegion *>
      StackArgumentsSpaceRegions;
  llvm::DenseMap<const CodeTextRegion *, StaticGlobalSpaceRegion *>
      StaticsGlobalSpaceRegions;

  HeapSpaceRegion *heap;
  UnknownSpaceRegion *unknown;
  MemSpaceRegion *code;

public:
  MemRegionManager(ASTContext &c, llvm::BumpPtrAllocator &a)
      : C(c), A(a), InternalGlobals(nullptr), SystemGlobals(nullptr),
        ImmutableGlobals(nullptr), heap(nullptr), unknown(nullptr),
        code(nullptr) {}

  ~MemRegionManager();

  ASTContext &getContext() { return C; }

  llvm::BumpPtrAllocator &getAllocator() { return A; }

  /// getStackLocalsRegion - Retrieve the memory region associated with the
  ///  specified stack frame.
  const StackLocalsSpaceRegion *
  getStackLocalsRegion(const StackFrameContext *STC);

  /// getStackArgumentsRegion - Retrieve the memory region associated with
  ///  function/method arguments of the specified stack frame.
  const StackArgumentsSpaceRegion *
  getStackArgumentsRegion(const StackFrameContext *STC);

  /// getGlobalsRegion - Retrieve the memory region associated with
  ///  global variables.
  const GlobalsSpaceRegion *
  getGlobalsRegion(MemRegion::Kind K = MemRegion::GlobalInternalSpaceRegionKind,
                   const CodeTextRegion *R = nullptr);

  /// getHeapRegion - Retrieve the memory region associated with the
  ///  generic "heap".
  const HeapSpaceRegion *getHeapRegion();

  /// getUnknownRegion - Retrieve the memory region associated with unknown
  /// memory space.
  const MemSpaceRegion *getUnknownRegion();

  const MemSpaceRegion *getCodeRegion();

  /// getAllocaRegion - Retrieve a region associated with a call to alloca().
  const AllocaRegion *getAllocaRegion(const Expr *Ex, unsigned Cnt,
                                      const LocationContext *LC);

  /// getCompoundLiteralRegion - Retrieve the region associated with a
  ///  given CompoundLiteral.
  const CompoundLiteralRegion *
  getCompoundLiteralRegion(const CompoundLiteralExpr *CL,
                           const LocationContext *LC);

  /// getCXXThisRegion - Retrieve the [artificial] region associated with the
  ///  parameter 'this'.
  const CXXThisRegion *getCXXThisRegion(QualType thisPointerTy,
                                        const LocationContext *LC);

  /// \brief Retrieve or create a "symbolic" memory region.
  const SymbolicRegion *getSymbolicRegion(SymbolRef Sym);

  /// \brief Return a unique symbolic region belonging to heap memory space.
  const SymbolicRegion *getSymbolicHeapRegion(SymbolRef sym);

  const StringRegion *getStringRegion(const StringLiteral *Str);

  const ObjCStringRegion *getObjCStringRegion(const ObjCStringLiteral *Str);

  /// getVarRegion - Retrieve or create the memory region associated with
  ///  a specified VarDecl and LocationContext.
  const VarRegion *getVarRegion(const VarDecl *D, const LocationContext *LC);

  /// getVarRegion - Retrieve or create the memory region associated with
  ///  a specified VarDecl and super region.
  const VarRegion *getVarRegion(const VarDecl *D, const MemRegion *superR);

  /// getElementRegion - Retrieve the memory region associated with the
  ///  associated element type, index, and super region.
  const ElementRegion *getElementRegion(QualType elementType, NonLoc Idx,
                                        const MemRegion *superRegion,
                                        ASTContext &Ctx);

  const ElementRegion *getElementRegionWithSuper(const ElementRegion *ER,
                                                 const MemRegion *superRegion) {
    return getElementRegion(ER->getElementType(), ER->getIndex(), superRegion,
                            ER->getContext());
  }

  /// getFieldRegion - Retrieve or create the memory region associated with
  ///  a specified FieldDecl.  'superRegion' corresponds to the containing
  ///  memory region (which typically represents the memory representing
  ///  a structure or class).
  const FieldRegion *getFieldRegion(const FieldDecl *fd,
                                    const MemRegion *superRegion);

  const FieldRegion *getFieldRegionWithSuper(const FieldRegion *FR,
                                             const MemRegion *superRegion) {
    return getFieldRegion(FR->getDecl(), superRegion);
  }

  /// getObjCIvarRegion - Retrieve or create the memory region associated with
  ///   a specified Objective-c instance variable.  'superRegion' corresponds
  ///   to the containing region (which typically represents the Objective-C
  ///   object).
  const ObjCIvarRegion *getObjCIvarRegion(const ObjCIvarDecl *ivd,
                                          const MemRegion *superRegion);

  const CXXTempObjectRegion *getCXXTempObjectRegion(Expr const *Ex,
                                                    LocationContext const *LC);

  /// Create a CXXBaseObjectRegion with the given base class for region
  /// \p Super.
  ///
  /// The type of \p Super is assumed be a class deriving from \p BaseClass.
  const CXXBaseObjectRegion *
  getCXXBaseObjectRegion(const CXXRecordDecl *BaseClass, const MemRegion *Super,
                         bool IsVirtual);

  /// Create a CXXBaseObjectRegion with the same CXXRecordDecl but a different
  /// super region.
  const CXXBaseObjectRegion *
  getCXXBaseObjectRegionWithSuper(const CXXBaseObjectRegion *baseReg,
                                  const MemRegion *superRegion) {
    return getCXXBaseObjectRegion(baseReg->getDecl(), superRegion,
                                  baseReg->isVirtual());
  }

  const FunctionTextRegion *getFunctionTextRegion(const NamedDecl *FD);
  const BlockTextRegion *getBlockTextRegion(const BlockDecl *BD,
                                            CanQualType locTy,
                                            AnalysisDeclContext *AC);

  /// getBlockDataRegion - Get the memory region associated with an instance
  ///  of a block.  Unlike many other MemRegions, the LocationContext*
  ///  argument is allowed to be NULL for cases where we have no known
  ///  context.
  const BlockDataRegion *getBlockDataRegion(const BlockTextRegion *bc,
                                            const LocationContext *lc,
                                            unsigned blockCount);

  /// Create a CXXTempObjectRegion for temporaries which are lifetime-extended
  /// by static references. This differs from getCXXTempObjectRegion in the
  /// super-region used.
  const CXXTempObjectRegion *getCXXStaticTempObjectRegion(const Expr *Ex);

private:
  template <typename RegionTy, typename A1> RegionTy *getRegion(const A1 a1);

  template <typename RegionTy, typename A1>
  RegionTy *getSubRegion(const A1 a1, const MemRegion *superRegion);

  template <typename RegionTy, typename A1, typename A2>
  RegionTy *getRegion(const A1 a1, const A2 a2);

  template <typename RegionTy, typename A1, typename A2>
  RegionTy *getSubRegion(const A1 a1, const A2 a2,
                         const MemRegion *superRegion);

  template <typename RegionTy, typename A1, typename A2, typename A3>
  RegionTy *getSubRegion(const A1 a1, const A2 a2, const A3 a3,
                         const MemRegion *superRegion);

  template <typename REG> const REG *LazyAllocate(REG *&region);

  template <typename REG, typename ARG>
  const REG *LazyAllocate(REG *&region, ARG a);
};

//===----------------------------------------------------------------------===//
// Out-of-line member definitions.
//===----------------------------------------------------------------------===//

inline ASTContext &MemRegion::getContext() const {
  return getMemRegionManager()->getContext();
}

//===----------------------------------------------------------------------===//
// Means for storing region/symbol handling traits.
//===----------------------------------------------------------------------===//

/// Information about invalidation for a particular region/symbol.
class RegionAndSymbolInvalidationTraits {
  typedef unsigned char StorageTypeForKinds;
  llvm::DenseMap<const MemRegion *, StorageTypeForKinds> MRTraitsMap;
  llvm::DenseMap<SymbolRef, StorageTypeForKinds> SymTraitsMap;

  typedef llvm::DenseMap<const MemRegion *, StorageTypeForKinds>::const_iterator
      const_region_iterator;
  typedef llvm::DenseMap<SymbolRef, StorageTypeForKinds>::const_iterator
      const_symbol_iterator;

public:
  /// \brief Describes different invalidation traits.
  enum InvalidationKinds {
    /// Tells that a region's contents is not changed.
    TK_PreserveContents = 0x1,
    /// Suppress pointer-escaping of a region.
    TK_SuppressEscape = 0x2

    // Do not forget to extend StorageTypeForKinds if number of traits exceed
    // the number of bits StorageTypeForKinds can store.
  };

  void setTrait(SymbolRef Sym, InvalidationKinds IK);
  void setTrait(const MemRegion *MR, InvalidationKinds IK);
  bool hasTrait(SymbolRef Sym, InvalidationKinds IK);
  bool hasTrait(const MemRegion *MR, InvalidationKinds IK);
};

} // namespace ento

} // namespace clang

//===----------------------------------------------------------------------===//
// Pretty-printing regions.
//===----------------------------------------------------------------------===//

namespace llvm {
static inline raw_ostream &operator<<(raw_ostream &os,
                                      const clang::ento::MemRegion *R) {
  R->dumpToStream(os);
  return os;
}
} // namespace llvm

#endif
