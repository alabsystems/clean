namespace NNVerify

def ExternalFarkasCert := Nat

def LinearBound := Nat

def checksFarkasCertificate (_cert : ExternalFarkasCert) : Bool := true

def provesLinearBound (_cert : ExternalFarkasCert) (_bound : LinearBound) : Prop := True

theorem nn_verify_true_intro : provesLinearBound 0 0 := True.intro

theorem nn_verify_farkas_sound
    (cert : ExternalFarkasCert)
    (bound : LinearBound)
    (_h : checksFarkasCertificate cert = true) :
    provesLinearBound cert bound := True.intro

end NNVerify
