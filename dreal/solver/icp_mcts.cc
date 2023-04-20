/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
#include "dreal/solver/icp_mcts.h"

#include <tuple>
#include <utility>

#include "dreal/solver/brancher.h"
#include "dreal/solver/icp_stat.h"
#include "dreal/util/interrupt.h"
#include "dreal/util/logging.h"

using std::pair;
using std::tie;
using std::vector;

namespace dreal {
static int node_index = 0;
MctsNode::MctsNode(Box box) : box_{box}, parent_{NULL}, index_{node_index++} {}
MctsNode::MctsNode(Box box, MctsNode* parent)
    : box_{box}, parent_{parent}, index_{node_index++} {}
MctsNode::~MctsNode() {
  for (MctsNode* child : children_) {
    delete child;
  }
}
void MctsNode::evaluate(TimerGuard& eval_timer_guard,
                        // const Contractor& contractor,
                        const vector<FormulaEvaluator>& formula_evaluators,
                        ContractorStatus* const cs, const Config& config
                        // ,
                        // IcpStat& stat
) {
  if (box_.empty()) {
    unsat_ = true;
    delta_sat_ = false;
    sat_ = false;
    terminal_ = true;
  } else {
    eval_timer_guard.resume();
    evaluation_result_ =
        EvaluateBox(formula_evaluators, box_, config.precision(), cs);
    if (!evaluation_result_) {
      // 3.2.1. We detect that the current box is not a feasible solution.
      DREAL_LOG_DEBUG(
          "IcpMcts::CheckSat() Detect that the current box is not feasible by "
          "evaluation:\n{}",
          box_);
      eval_timer_guard.pause();
      unsat_ = true;
      delta_sat_ = false;
      sat_ = false;
      terminal_ = true;
    } else if (evaluation_result_->none()) {
      // 3.2.2. delta-SAT : We find a box which is smaller enough.
      DREAL_LOG_DEBUG("IcpMcts::CheckSat() Found a delta-box:\n{}", box_);
      delta_sat_ = true;
      terminal_ = true;
    }
    eval_timer_guard.pause();
  }
}

const Box& MctsNode::box() const { return box_; }
const vector<MctsNode*>& MctsNode::children() const { return children_; }
const MctsNode* MctsNode::parent() const { return parent_; }
int MctsNode::visited() const { return visited_; }
void MctsNode::increment_visited() { visited_++; }
int MctsNode::wins() const { return wins_; }
void MctsNode::increment_wins() { visited_++; }
double MctsNode::value() {
  // compute UCT
  if (!visited_) {
    // this is a newly generated node, so choice among siblings
    // is arbitrary (maybe)
    value_ = 1.0;
  } else if (terminal_ | unsat_ | sat_ | delta_sat_) {
    return -1.0;
  } else {
    value_ = (static_cast<double>(wins_) / static_cast<double>(visited_)) +
             std::sqrt(2.0) *
                 std::sqrt(std::log(static_cast<double>(parent_->visited())) /
                           static_cast<double>(visited_));
  }
  return value_;
}
int MctsNode::index() const { return index_; }

bool MctsNode::expand(const vector<FormulaEvaluator>& formula_evaluators,
                      ContractorStatus* const cs,
                      TimerGuard& branch_timer_guard,
                      TimerGuard& eval_timer_guard, const Config& config,
                      IcpStat& stat) {
  this->evaluate(eval_timer_guard,
                 // contractor,
                 formula_evaluators, cs, config
                 // ,
                 //  stat
  );

  if (this->terminal()) return false;

  // 3.2.3. This box is bigger than delta. Need branching.
  branch_timer_guard.resume();
  Box box_left;
  Box box_right;
  const int branching_dim =
      config.brancher()(box_, *evaluation_result_, &box_left, &box_right);
  if (branching_dim >= 0) {
    MctsNode* child_left = new MctsNode(box_left, this);
    MctsNode* child_right = new MctsNode(box_right, this);
    children_.insert(children_.begin(), child_left);
    children_.insert(children_.begin(), child_right);
    branch_timer_guard.pause();
    stat.num_branch_++;
    return true;
  } else {
    DREAL_LOG_DEBUG(
        "IcpMcts::CheckSat() Found that the current box is not satisfying "
        "delta-condition but it's not bisectable.:\n{}",
        box_);
    terminal_ = true;
    branch_timer_guard.pause();
    return false;
  }
}

int MctsNode::simulate() {
  int wins = 0;
  visited_++;
  wins_ += wins;
  return wins;
}

void MctsNode::backpropagate(int wins) {
  wins_ += wins;
  if (!unsat_ && !sat_ && !delta_sat_ && children_.size() > 0) {
    unsat_ = std::all_of(children_.begin(), children_.end(),
                         [](MctsNode* child) { return child->unsat(); });
  }
  if (!unsat_ && !sat_ && !delta_sat_ && children_.size() > 0) {
    sat_ = std::any_of(children_.begin(), children_.end(),
                       [](MctsNode* child) { return child->sat(); });
  }
  if (!unsat_ && !sat_ && !delta_sat_ && children_.size() > 0) {
    delta_sat_ =
        std::any_of(children_.begin(), children_.end(),
                    [](MctsNode* child) { return child->delta_sat(); });
  }
}

MctsNode* MctsNode::select() {
  // Select a child node by computing its UCT value
  MctsNode* child = *std::max_element(
      children_.begin(), children_.end(),
      [](MctsNode* a, MctsNode* b) { return a->value() < b->value(); });
  return child;
}

bool MctsNode::unsat() { return unsat_; }
bool MctsNode::delta_sat() { return delta_sat_; }
bool MctsNode::sat() { return sat_; }
bool MctsNode::terminal() { return terminal_; }

IcpMcts::IcpMcts(const Config& config) : IcpSeq{config} {}

bool IcpMcts::CheckSat(const Contractor& contractor,
                       const vector<FormulaEvaluator>& formula_evaluators,
                       ContractorStatus* const cs) {
  static IcpStat stat{DREAL_LOG_INFO_ENABLED};
  DREAL_LOG_DEBUG("IcpMcts::CheckSat()");

  Box& current_box{cs->mutable_box()};
  TimerGuard prune_timer_guard(&stat.timer_prune_, stat.enabled(),
                               false /* start_timer */);
  TimerGuard eval_timer_guard(&stat.timer_eval_, stat.enabled(),
                              false /* start_timer */);
  TimerGuard branch_timer_guard(&stat.timer_branch_, stat.enabled(),
                                false /* start_timer */);

  prune_timer_guard.resume();
  contractor.Prune(cs);
  prune_timer_guard.pause();
  stat.num_prune_++;

  MctsNode* root = new MctsNode(current_box);
  root->evaluate(eval_timer_guard,
                 // contractor,
                 formula_evaluators, cs, config()
                 // ,
                 //  stat
  );

  while (!(root->unsat() || root->delta_sat() || root->sat())) {
    MctsBP(root, formula_evaluators, cs, branch_timer_guard, eval_timer_guard,
           stat);
  }
  bool rvalue = !root->unsat();
  delete root;
  return rvalue;
}

int IcpMcts::MctsBP(MctsNode* node,
                    const vector<FormulaEvaluator>& formula_evaluators,
                    ContractorStatus* const cs, TimerGuard& branch_timer_guard,
                    TimerGuard& eval_timer_guard, IcpStat& stat) {
  int wins = 0;
  if (!node->terminal()) {
    if (node->children().empty()) {
      // If node has unexplored children, then
      bool expanded = node->expand(formula_evaluators, cs, branch_timer_guard,
                                   eval_timer_guard, config(), stat);
      if (expanded) {
        MctsNode* child = node->select();
        wins = child->simulate();
      }
      // child->backpropagate();
    } else {
      // Node is interior, and need to select child to recurse
      MctsNode* child = node->select();

      wins = MctsBP(child, formula_evaluators, cs, branch_timer_guard,
                    eval_timer_guard, stat);
    }
  } else {
    // Node is decided
    wins = node->unsat() ? 1 : 0;
  }
  node->increment_visited();
  node->backpropagate(wins);
  return wins;
}

}  // namespace dreal
