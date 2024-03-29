// ===========================================================================
// SWEN90010 2018 - Assignment 3 Submission
// by Mengnan Shi(802123) Ye Yan(816694)
// ===========================================================================

module icd
open util/ordering[State] as ord

// =========================== System State ==================================
// a type for storing amounts of Joules
sig Joules {}

// the initial number of joules to deliver (30)
one sig InitialJoulesToDeliver extends Joules {}

// we ignore the clinical assistants for simplicity in this model
abstract sig Role {}
one sig Cardiologist, Patient extends Role {}

one sig UndefinedRole extends Role {}

// principals have associated roles
sig Principal {
  roles : set Role
}

// an abstract signature for network messages
abstract sig Message {
  source : Principal
}

// ChangeSettingsRequest messages
// Note: we ignore the tachybound part to keep things tractable
sig ChangeSettingsMessage extends Message {
  joules_to_deliver : Joules
}

// ModeOn message
sig ModeOnMessage extends Message {
}

// Modes: either On or Off
abstract sig Mode {}
one sig ModeOn, ModeOff extends Mode {}

// meta information in the model that identifies the last action performed
abstract sig Action {
  who : Principal  // indentifies which principal caused the action
}

// Network actions
sig SendModeOn, RecvModeOn,
    SendChangeSettings, RecvChangeSettings
    extends Action {}

// represents the occurrence of attacker actions
one sig AttackerAction extends Action {}

// a dummy action which will be the "last action" in the initial state
// we do this just to make sure that every state has a last action
one sig DummyInitialAction extends Action {}

// The system state
sig State {
  network : lone Message,          // CAN Bus state: holds up to one message
  icd_mode : Mode,                 // whether ICD system is in on or off mode
  impulse_mode : Mode,             // whether the impulse generator is on or off
  joules_to_deliver : Joules,      // joules to deliver for ventrical fibrillation
  authorised_card : Principal,     // the authorised cardiologist
  last_action : Action,            // identifies the most recent action performed
}

// an axiom that restricts the model to never allow more than one messasge on
// the network at a time; a simplifying assumption to ease the analysis
fact {
  all s : State | lone s.network
}

// =========================== Initial State =================================

// The initial state of the system:
//   - empty network,
//   - ICD and impulse generator both off
//   - joules to deliver at initial value
//   - the authorised cardiologist is really a cardiologist
//   - last_action set to the dummy value
pred Init[s : State] {
  no s.network and s.icd_mode = ModeOff and s.impulse_mode = ModeOff
  and s.joules_to_deliver = InitialJoulesToDeliver and
  Cardiologist in s.authorised_card.roles and
  s.last_action = DummyInitialAction
}

// =========================== Actions =======================================

// Models the action in which a ModeOn message is sent on the network by the
// authorised cardiologist.
// Precondition: none
// Postcondition: network now contains a ModeOn message from the authorised cardiologist
//                last_action is SendModeOn for the message's sender
//                and nothing else changes
pred send_mode_on[s, s' : State] {
   some m : ModeOnMessage | m.source = s.authorised_card and m.source.roles in Cardiologist =>
      s'.network = s.network + m and
      s'.icd_mode = s.icd_mode and
      s'.impulse_mode = s.impulse_mode and
      s'.joules_to_deliver = s.joules_to_deliver and
      s'.authorised_card = s.authorised_card and
      s'.last_action in SendModeOn and
      s'.last_action.who = m.source
   else
      // in other cases, nothing should change
      s' = s
}

// Models the action in which a valid ModeOn message is received by the
// ICD from the authorised cardiologist, causing the ICD system's mode to change
// from Off to On and the message to be removed from the network
// Precondition: A valid ModeOn message is received by the ICD from the authorised cardiologist
// Postcondition: network now contains no message
//                icd_mode = ModeOn
//                last_action in RecvModeOn and
//                last_action.who = the source of the ModeOn message
//                and nothing else changes
pred recv_mode_on[s, s' : State] {
   one m: s.network | m in ModeOnMessage and m.source in s.authorised_card =>
      s'.network = s.network - m and
      s'.icd_mode = ModeOn and
      s'.impulse_mode = ModeOn and
      s'.joules_to_deliver = s.joules_to_deliver and
      s'.authorised_card = s.authorised_card and
      s'.last_action in RecvModeOn and
      s'.last_action.who = m.source
   else
      // in other cases, nothing should change
      s'= s
}

// Models the action in which a valid ChangeSettingsRequest message is sent
// on the network, from the authorised cardiologist, specifying the new quantity of 
// joules to deliver for ventrical fibrillation.
// Precondition: The system is turned off
// Postcondition: network now contains a ChangeSettingsMessage message from the authorised
//                   The message is from a the authorised cardiologist
//                   The message contains a value of Joules
//                last_action in SendChangeSettings and
//                last_action.who = the source of the ChangeSettingsMessage
//                and nothing else changes
pred send_change_settings[s, s' : State] {
   some m : ChangeSettingsMessage | m.source in s.authorised_card and m.joules_to_deliver in Joules and m.source.roles in Cardiologist =>
      s'.network = s.network + m and
      s'.icd_mode = s.icd_mode and
      s'.impulse_mode = s.impulse_mode and
      s'.joules_to_deliver = s.joules_to_deliver and
      s'.authorised_card = s.authorised_card and
      s'.last_action in SendChangeSettings and
      s'.last_action.who = m.source
   else
      // in other cases, nothing should change
      s'=s
}

// Models the action in which a valid ChangeSettingsRequest message is received
// by the ICD, from the authorised cardiologist, causing the current joules to be 
// updated to that contained in the message and the message to be removed from the 
// network.
// Precondition: The system is in ModeOff mode
//               And a valid ChangeSettingsRequest message is received
// Postcondition: network now contains a message with a ChangeSettingsMessage command
//                last_action in RecvChangeSettings and
//                last_action.who = the source of the ChangeSettingsMessage
//                and nothing else changes
pred recv_change_settings[s, s' : State] {
   s.icd_mode in ModeOff and
   one m: s.network | m in ChangeSettingsMessage and m.source in s.authorised_card and m.joules_to_deliver in Joules =>
      s'.network = s.network - m and
      s'.icd_mode = s.icd_mode and
      s'.impulse_mode = s.impulse_mode and
      s'.joules_to_deliver = m.joules_to_deliver and
      s'.authorised_card = s.authorised_card and
      s'.last_action in RecvChangeSettings and
      s'.last_action.who = m.source
   else
      // in other cases, nothing should change
      s'=s
}

// =========================== Attacker Actions ==============================

// Models the actions of a potential attacker that has access to the network
// The only part of the system state that the attacker can possibly change
// is that of the network
//
// NOTE: In the initial template you are given, the attacker
// is modelled as being able to modify the network contents arbitrarily.
// However, for later parts of the assignment you will change this definition
// to only permit certain kinds of modifications to the state of the network.
// When doing so, ensure you update the following line that describes the
// attacker's abilities.
//
// Attacker's abilities: can modify network contents arbitrarily
//                       <UPDATE HERE>
//
// Precondition: none
// Postcondition: network state changes in accordance with attacker's abilities
//                last_action is AttackerAction
//                and nothing else changes
pred attacker_action[s, s' : State] {
   s'.icd_mode = s.icd_mode and
   s'.joules_to_deliver = s.joules_to_deliver and
   s'.impulse_mode = s.impulse_mode and
   s'.authorised_card = s.authorised_card and
   s'.last_action = AttackerAction
//and
  //all m: s'.network | m.source.roles = UndefinedRole
}

// =========================== State Transitions and Traces ==================

// State transitions occur via the various actions of the system above
// including those of the attacker.
pred state_transition[s, s' : State] {
   send_mode_on[s,s']
   or recv_mode_on[s,s']
   or send_change_settings[s,s']
   or recv_change_settings[s,s']
   or attacker_action[s,s']
}

// Define the linear ordering on states to be that generated by the
// state transitions above, defining execution traces to be sequences
// of states in which each state follows in the sequence from the last
// by a state transition.
fact state_transition_ord {
   all s: State, s': ord/next[s] {
      state_transition[s,s'] and s' != s
   }
}

// The initial state is first in the order, i.e. all execution traces
// that we model begin in the initial state described by the Init predicate
fact init_state {
   all s: ord/first {
      Init[s]
   }
}

// =========================== Properties ====================================

assert icd_never_off_after_on {
   all s : State | all s' : ord/nexts[s] | 
      s.icd_mode = ModeOn implies s'.icd_mode = ModeOn
}

check icd_never_off_after_on for 10 expect 0

pred bothOn[s: State]{
  all s: State | s.icd_mode in ModeOn => s.impulse_mode in ModeOn	
}

pred bothOff[s: State]{
  all s: State | s.icd_mode in ModeOff => s.impulse_mode in ModeOff	
}

pred inv[s : State] {
  all s: State | bothOn[s] and bothOff[s]
}

assert inv_always {
  inv[ord/first] and all s : ord/nexts[ord/first] | inv[s]
}

// Check that the invariant is never violated during 15
// state transitions
check inv_always for 10
// This assertion holds.
// The system starts with both the icd_mode and the impulse_mode is turned off, 
// which indicates that this assertion holds (pred of "bothOff")
// When a ModeOnMessage is received by the system, both of the two components are 
// switched on (pred of "bothOn")
//       counterexamples, so you can interpret them

// Check that all the RecvChangeSettings commands are not sent by a Patient 
// when there is no attacker exists.
assert unexplained_assertion {
  all s : State | (all s' : State | s'.last_action not in AttackerAction) =>
      s.last_action in RecvChangeSettings =>
      Patient not in s.last_action.who.roles
}

check unexplained_assertion for 10
// This assertion holds.
// There are two kinds ok roles: the Patient and the Cardiologist.
// If no data is altered (no attaker), the patient cannot generate a 
// RecvChangeSettings message.

// Check that the device turns on only after properly instructed to
// i.e. that the RecvModeOn action occurs only after a SendModeOn action has occurred
assert turns_on_safe {
   all s: State | all s' : ord/next[s] | 
//      s.last_action in SendModeOn => s'.last_action in RecvModeOn
		s'.last_action in RecvModeOn => s.last_action in SendModeOn
}

// NOTE: you may want to adjust these thresholds for your own use
check turns_on_safe for 10
// <FILL IN HERE: does the assertion hold in the updated attacker model in which
// the attacker cannot guess Principal ids? why / why not?>
// what additional restrictions need to be added to the attacker model?



// Attacks still permitted by the updated attacker model:
// 
// <FILL IN HERE>


// Relationship to our HAZOP study:
//
// <FILL IN HERE>
