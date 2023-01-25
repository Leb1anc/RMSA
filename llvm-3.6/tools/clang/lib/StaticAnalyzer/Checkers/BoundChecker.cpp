#include "ClangSACheckers.h"
#include "clang/AST/CharUnits.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExprEngine.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/MemRegion.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace ento;

namespace {

class BoundChecker : public Checker<check::Location> {
  mutable std::unique_ptr<BuiltinBug> BT;

  enum OOB_Kind { OOB_LowerBA, OOB_UpperBA };

  void reportOOB(CheckerContext &C, ProgramStateRef errorState,
                 OOB_Kind kind) const;

public:
  void checkLocation(SVal l, bool isLoad, const Stmt *S,
                     CheckerContext &C) const;
};

class OffsetInfo {
private:
  const SubRegion *subRegion;
  SVal offset;

  OffsetInfo() : subRegion(nullptr), offset(UnknownVal()) {}

public:
  OffsetInfo(const SubRegion *_region, SVal _offset)
      : subRegion(_region), offset(_offset) {}

  NonLoc getOffset() const { return offset.castAs<NonLoc>(); }

  const SubRegion *getRegion() const { return subRegion; }

  static OffsetInfo computeOffset(ProgramStateRef state,
                                  SValBuilder &svalBuilder, SVal location);

  void dump() const;
  void dumpToStream(raw_ostream &os) const;
};

} // end namespace

static inline SVal getValue(SVal val, SValBuilder &svalBuilder) {
  return val.getAs<UndefinedVal>() ? svalBuilder.makeArrayIndex(0) : val;
}

static inline SVal scaleValue(ProgramStateRef state, NonLoc baseVal,
                              CharUnits scaling, SValBuilder &sb) {
  return sb.evalBinOpNN(state, BO_Mul, baseVal,
                        sb.makeArrayIndex(scaling.getQuantity()),
                        sb.getArrayIndexType());
}

static SVal addValue(ProgramStateRef state, SVal x, SVal y,
                     SValBuilder &svalBuilder) {

  if (x.isUnknownOrUndef() || y.isUnknownOrUndef())
    return UnknownVal();

  return svalBuilder.evalBinOpNN(state, BO_Add, x.castAs<NonLoc>(),
                                 y.castAs<NonLoc>(),
                                 svalBuilder.getArrayIndexType());
}

OffsetInfo OffsetInfo::computeOffset(ProgramStateRef state,
                                     SValBuilder &svalBuilder, SVal location) {
  const MemRegion *region = location.getAsRegion();
  SVal offset = UndefinedVal();

  while (region) {
    switch (region->getKind()) {
    default: {
      if (const SubRegion *subReg = dyn_cast<SubRegion>(region)) {
        offset = getValue(offset, svalBuilder);
        if (!offset.isUnknownOrUndef())
          return OffsetInfo(subReg, offset);
      }
      return OffsetInfo();
    }
    case MemRegion::ElementRegionKind: {
      const ElementRegion *elemReg = cast<ElementRegion>(region);
      SVal index = elemReg->getIndex();
      if (!index.getAs<NonLoc>())
        return OffsetInfo();
      QualType elemType = elemReg->getElementType();
      // If the element is an incomplete type, go no further.
      ASTContext &astContext = svalBuilder.getContext();
      if (elemType->isIncompleteType())
        return OffsetInfo();

      // Update the offset.
      offset = addValue(state, getValue(offset, svalBuilder),
                        scaleValue(state, index.castAs<NonLoc>(),
                                   astContext.getTypeSizeInChars(elemType),
                                   svalBuilder),
                        svalBuilder);

      if (offset.isUnknownOrUndef())
        return OffsetInfo();

      region = elemReg->getSuperRegion();
      continue;
    }
    }
  }
  return OffsetInfo();
}

static SVal computeHeadLoc(SValBuilder &svalBuilder, const MemRegion *region) {
  while (true)
    switch (region->getKind()) {
    default:
      return svalBuilder.makeZeroArrayIndex();
    case MemRegion::SymbolicRegionKind:
      // FIXME: improve this later by tracking symbolic lower bounds
      // for symbolic regions.
      return UnknownVal();
    case MemRegion::ElementRegionKind:
      region = cast<SubRegion>(region)->getSuperRegion();
      continue;
    }
}

void BoundChecker::checkLocation(SVal location, bool isLoad, const Stmt *LoadS,
                                 CheckerContext &checkerContext) const {

  (void)isLoad, (void)LoadS;

  ProgramStateRef state = checkerContext.getState();
  ProgramStateRef originalState = state;

  SValBuilder &svalBuilder = checkerContext.getSValBuilder();

  const OffsetInfo &offsetInfo =
      OffsetInfo::computeOffset(state, svalBuilder, location);

  if (!offsetInfo.getRegion())
    return;
  SVal headBegin = computeHeadLoc(svalBuilder, offsetInfo.getRegion());

  if (Optional<NonLoc> NV = headBegin.getAs<NonLoc>()) {
    SVal lowerBound =
        svalBuilder.evalBinOpNN(state, BO_LT, offsetInfo.getOffset(), *NV,
                                svalBuilder.getConditionType());

    Optional<NonLoc> lowerBoundToCheck = lowerBound.getAs<NonLoc>();
    if (!lowerBoundToCheck)
      return;

    ProgramStateRef state_precedesLowerBound, state_withinLowerBound;
    std::tie(state_precedesLowerBound, state_withinLowerBound) =
        state->assume(*lowerBoundToCheck);

    // Are we constrained enough to definitely precede the lower bound?
    if (state_precedesLowerBound && !state_withinLowerBound) {
      reportOOB(checkerContext, state_precedesLowerBound, OOB_LowerBA);
      return;
    }

    // Otherwise, assume the constraint of the lower bound.
    assert(state_withinLowerBound);
    state = state_withinLowerBound;
  }

  do {
    // CHECK UPPER BOUND: Is byteOffset >= extent(baseRegion)?  If so,
    // we are doing a load/store after the last valid offset.
    DefinedOrUnknownSVal extentVal =
        offsetInfo.getRegion()->getExtent(svalBuilder);
    if (!extentVal.getAs<NonLoc>())
      break;

    SVal upperbound = svalBuilder.evalBinOpNN(
        state, BO_GE, offsetInfo.getOffset(), extentVal.castAs<NonLoc>(),
        svalBuilder.getConditionType());

    Optional<NonLoc> upperboundToCheck = upperbound.getAs<NonLoc>();
    if (!upperboundToCheck)
      break;

    ProgramStateRef state_exceedsUpperBound, state_withinUpperBound;
    std::tie(state_exceedsUpperBound, state_withinUpperBound) =
        state->assume(*upperboundToCheck);

    if (state_exceedsUpperBound && state_withinUpperBound) {
      if (state->isTainted(offsetInfo.getOffset()))
        reportOOB(checkerContext, state_exceedsUpperBound, OOB_LowerBA);
      return;
    }

    // If we are constrained enough to definitely exceed the upper bound,
    // report.
    if (state_exceedsUpperBound) {
      assert(!state_withinUpperBound);
      reportOOB(checkerContext, state_exceedsUpperBound, OOB_UpperBA);
      return;
    }

    assert(state_withinUpperBound);
    state = state_withinUpperBound;
  } while (false);

  if (state != originalState)
    checkerContext.addTransition(state);
}

void BoundChecker::reportOOB(CheckerContext &checkerContext,
                             ProgramStateRef errorState, OOB_Kind kind) const {

  ExplodedNode *errorNode = checkerContext.generateSink(errorState);
  if (!errorNode)
    return;

  if (!BT)
    BT.reset(new BuiltinBug(this, "Out-of-bound access"));

  // FIXME: This diagnostics are preliminary.  We should get far better
  // diagnostics for explaining buffer overruns.

  SmallString<256> buf;
  llvm::raw_svector_ostream os(buf);
  os << "Out of bound memory access ";
  switch (kind) {
  case OOB_LowerBA:
    os << "(accessed memory precedes Lower memory block)";
    break;
  case OOB_UpperBA:
    os << "(access exceeds upper limit of memory block)";
    break;
  }

  checkerContext.emitReport(new BugReport(*BT, os.str(), errorNode));
}

void OffsetInfo::dump() const { dumpToStream(llvm::errs()); }

void OffsetInfo::dumpToStream(raw_ostream &os) const {
  os << "raw_offset_v2{" << getRegion() << ',' << getOffset() << '}';
}

void ento::registerBoundChecker(CheckerManager &mgr) {
  mgr.registerChecker<BoundChecker>();
}

// namespace
