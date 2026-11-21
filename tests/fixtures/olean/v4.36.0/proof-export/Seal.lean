module
namespace Seal
private theorem hidden : True := True.intro
public theorem exportedProof : True := hidden
public axiom gap : True
public theorem usesGap : True := gap
end Seal
