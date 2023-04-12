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

#include <random>
#include <tuple>
#include <utility>

#include "dreal/solver/brancher.h"
#include "dreal/solver/icp_stat.h"
#include "dreal/util/box.h"
#include "dreal/util/interrupt.h"
#include "dreal/util/logging.h"
#include "dreal/util/optional.h"

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
    DREAL_LOG_INFO("Unsat");
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
      DREAL_LOG_INFO("Unsat");
    } else if (evaluation_result_->none()) {
      // 3.2.2. delta-SAT : We find a box which is small enough.
      DREAL_LOG_DEBUG("IcpMcts::CheckSat() Found a delta-box:\n{}", box_);
      delta_sat_ = true;
      terminal_ = true;
      DREAL_LOG_INFO("Delta-Sat");

      // Set the contractor_status box to this.box_
      Box& b = cs->mutable_box();
      b = box_;
    }
    eval_timer_guard.pause();
  }
}

const Box& MctsNode::box() const { return box_; }
const vector<MctsNode*>& MctsNode::children() const { return children_; }
const MctsNode* MctsNode::parent() const { return parent_; }
double MctsNode::visited() const { return visited_; }
void MctsNode::increment_visited() { visited_++; }
double MctsNode::wins() const { return wins_; }
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
                      ContractorStatus* const cs, const Contractor& contractor,
                      TimerGuard& branch_timer_guard,
                      TimerGuard& eval_timer_guard,
                      TimerGuard& prune_timer_guard, const Config& config,
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
    Box& contractor_box{cs->mutable_box()};
    prune_timer_guard.resume();
    contractor_box = box_left;
    contractor.Prune(cs);
    contractor_box = box_right;
    contractor.Prune(cs);
    prune_timer_guard.pause();
    stat.num_prune_++;

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

double MctsNode::simulate_box(
    Box& sim_box, const std::vector<FormulaEvaluator>& formula_evaluators,
    ContractorStatus* const cs, const Contractor& contractor,
    TimerGuard& eval_timer_guard, TimerGuard& prune_timer_guard,
    const Config& config, IcpStat& stat, std::default_random_engine& rnd) {
  // For each box in candidates
  //  Pick var to sample and sample num_samples times
  //  Add not unsat next_candidates to candidates

  int num_candidates = 10;
  int num_samples = 3;
  vector<Box*> candidates;
  Box& point_box{cs->mutable_box()};
  candidates.push_back(new Box(sim_box));

  int num_to_assign = 0;
  for (Variable v : sim_box.variables()) {
    Box::IntervalVector& values = sim_box.mutable_interval_vector();
    Box::Interval& interval = values[v.get_id() - 1];
    if (!interval.is_degenerated() && interval.diam() >= config.precision() &&
        !(interval.lb() == interval.mid() || interval.mid() == interval.ub())) {
      num_to_assign++;
    }
  }
  int depth = 0;
  while (!candidates.empty() && num_to_assign > 0) {
    depth++;
    vector<Box*> next_candidates;
    for (auto candidate = candidates.begin(); candidate != candidates.end();
         candidate++) {
      for (int i = 0; i < num_samples; i++) {
        Box* next_candidate = new Box(**candidate);
        // point_box = *next_candidate;
        Box::IntervalVector& values = next_candidate->mutable_interval_vector();

        double max_diam;
        int v_id;
        tie(max_diam, v_id) = next_candidate->FirstDiamGT(config.precision());
        if (v_id > -1 && max_diam > config.precision()) {
          Variable v = next_candidate->variables()[v_id];
          Box::Interval& interval = values[v_id];

          if (!interval.is_degenerated() &&
              interval.diam() >= config.precision() &&
              !(interval.lb() == interval.mid() ||
                interval.mid() == interval.ub())) {
            // Pick value for variable

            // random library supports only sampling from 0 to
            // std::numeric_limits<double>::max(), in the worst case, need to
            // sample lower: [-std::numeric_limits<double>::max(), 9) or
            // upper: [0, std::numeric_limits<double>::max()] here we'll
            // sample from [lb, midpoint] or [midpoint, ub] after choosing the
            // half interval to sample.

            std::bernoulli_distribution d(0.5);
            bool sample_lower = d(rnd);
            double lower =
                std::max(interval.lb(), -std::numeric_limits<double>::max());
            double upper =
                std::min(std::numeric_limits<double>::max(), interval.ub());
            double midpoint = interval.mid();
            // double diam = upper - lower;

            double r;
            if (sample_lower) {
              assert(midpoint - lower <= std::numeric_limits<double>::max());
              assert(midpoint - lower > 0);
              std::uniform_real_distribution<double> dist(lower, midpoint);
              // for (int i = 0; i < 100; i++) {
              r = dist(rnd);
              //   DREAL_LOG_DEBUG("IcpMcts::simulate_box() r = {}", r);
              // }
              if (r == -std::numeric_limits<double>::infinity()) {
                r = -std::numeric_limits<double>::max();
              }
            } else {
              assert(upper - midpoint <= std::numeric_limits<double>::max());
              assert(upper - midpoint > 0);
              std::uniform_real_distribution<double> dist(midpoint, upper);
              // r = dist(rnd);
              // for (int i = 0; i < 100; i++) {
              r = dist(rnd);
              //   DREAL_LOG_DEBUG("IcpMcts::simulate_box() r = {}", r);
              // }
              if (r == std::numeric_limits<double>::infinity()) {
                r = std::numeric_limits<double>::max();
              }
            }

            DREAL_LOG_DEBUG(
                "IcpMcts::simulate_box() sampling {}:{} = {} for:\n{}", v,
                interval, r, *next_candidate);
            double noise =
                std::min(config.precision() * 0.49, interval.diam() * 0.49);
            Box::Interval new_interval{std::max(interval.lb(), r - noise),
                                       std::min(interval.ub(), r + noise)};
            interval = interval & new_interval;
            values[v_id] = interval;
            DREAL_LOG_DEBUG(
                "IcpMcts::simulate_box() set interval {}:{} = {} for:\n{}", v,
                interval, r, *next_candidate);

            // Prune using the assignment
            // prune_timer_guard.resume();
            int& branching_point = cs->mutable_branching_point();
            branching_point = v.get_id() - 1;
          }
          point_box = *next_candidate;

          contractor.Prune(cs);
          prune_timer_guard.pause();
          stat.num_prune_++;
          stat.num_prune_--;

          DREAL_LOG_DEBUG(
              "IcpMcts::simulate_box() prune with sample results in "
              "box:\n{}",
              *next_candidate);

          DREAL_LOG_DEBUG(
              "IcpMcts::simulate_box() prune with sample results in "
              "point_box:\n{}",
              point_box);

          DREAL_LOG_DEBUG(
              "IcpMcts::simulate_box() prune with sample results in "
              "cs->box:\n{}",
              cs->mutable_box());

          delete next_candidate;
          next_candidate = new Box(cs->box());

          if (!next_candidate->empty()) {
            eval_timer_guard.resume();
            optional<DynamicBitset> evaluation_result = EvaluateBox(
                formula_evaluators, *next_candidate, config.precision(), cs);
            eval_timer_guard.pause();

            // DREAL_LOG_DEBUG(
            //     "IcpMcts::simulate_box() evalute box results:\n {} ",
            //     evaluation_result);

            DREAL_LOG_DEBUG(
                "IcpMcts::simulate_box() evalution_result: "
                "box:\n{}",
                *next_candidate);
            if (!evaluation_result) {
              // unsat
              delete next_candidate;
            } else if (evaluation_result->none()) {
              // delta sat
              delta_sat_box_ = Box(*next_candidate);
              delta_sat_ = true;
              terminal_ = true;
              break;

            } else {
              // still unknown
              next_candidates.push_back(next_candidate);
            }
          } else {
            // unsat
            delete next_candidate;
          }

        } else {
          delta_sat_box_ = Box(*next_candidate);
          delta_sat_ = true;
          terminal_ = true;
          break;
        }
      }
      if (delta_sat_) {
        break;
      }
    }
    // free candidates
    for (auto i = candidates.begin(); i != candidates.end(); ++i) {
      delete *i;
    }
    candidates.clear();

    // keep num_candidates next_candidates

    if (next_candidates.size() > 0) {
      std::uniform_int_distribution<int> dist(0, next_candidates.size() - 1);
      for (int j = 0; j < num_candidates; j++) {
        int candidate_index = dist(rnd);
        Box* candidate = new Box(*next_candidates[candidate_index]);
        candidates.insert(candidates.begin(), candidate);
      }
    } else {
      break;
    }
    for (auto i = next_candidates.begin(); i != next_candidates.end(); ++i) {
      delete *i;
    }
    next_candidates.clear();
    if (delta_sat_) {
      break;
    }
  }

  if (num_to_assign > 0) {
    return static_cast<double>(depth) / static_cast<double>(num_to_assign);
  } else {
    return 0;
  }
}

double MctsNode::simulate(
    const std::vector<FormulaEvaluator>& formula_evaluators,
    ContractorStatus* const cs, const Contractor& contractor,
    TimerGuard& eval_timer_guard, TimerGuard& prune_timer_guard,
    const Config& config, IcpStat& stat, std::default_random_engine& rnd) {
  double total_depth = 0;
  visited_++;
  int iterations = 1;
  int i = 1;
  for (; i <= iterations; i++) {
    // For each variable that is not degenerate, sample a value and assign it.
    Box sim_box{box_};
    double depth = this->simulate_box(sim_box, formula_evaluators, cs,
                                      contractor, eval_timer_guard,
                                      prune_timer_guard, config, stat, rnd);

    total_depth += depth;
    if (delta_sat_) {
      break;
    }
  }
  wins_ += (static_cast<double>(total_depth) / static_cast<double>(i));
  return (static_cast<double>(total_depth) / static_cast<double>(i));
}

void MctsNode::backpropagate(double wins) {
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
  if (unsat_ || sat_ || delta_sat_) {
    terminal_ = true;
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

  TimerGuard prune_timer_guard(&stat.timer_prune_, stat.enabled(),
                               false /* start_timer */);
  TimerGuard eval_timer_guard(&stat.timer_eval_, stat.enabled(),
                              false /* start_timer */);
  TimerGuard branch_timer_guard(&stat.timer_branch_, stat.enabled(),
                                false /* start_timer */);

  // prune_timer_guard.resume();
  // contractor.Prune(cs);
  // prune_timer_guard.pause();
  // stat.num_prune_++;

  prune_timer_guard.resume();
  contractor.Prune(cs);
  prune_timer_guard.pause();
  stat.num_prune_++;

  MctsNode* root = new MctsNode(Box(cs->box()));

  std::random_device rd;
  std::default_random_engine rnd(rd());

  root->simulate(formula_evaluators, cs, contractor, eval_timer_guard,
                 prune_timer_guard, config(), stat, rnd);

  while (!(root->unsat() || root->delta_sat() || root->sat())) {
    DREAL_LOG_INFO("[");
    MctsBP(root, formula_evaluators, cs, contractor, branch_timer_guard,
           eval_timer_guard, prune_timer_guard, stat, rnd);
    DREAL_LOG_INFO("]");
  }

  bool rvalue = !root->unsat();
  delete root;
  return rvalue;
}

double IcpMcts::MctsBP(MctsNode* node,
                       const vector<FormulaEvaluator>& formula_evaluators,
                       ContractorStatus* const cs, const Contractor& contractor,
                       TimerGuard& branch_timer_guard,
                       TimerGuard& eval_timer_guard,
                       TimerGuard& prune_timer_guard, IcpStat& stat,
                       std::default_random_engine& rnd) {
  double wins = 0;
  if (!node->terminal()) {
    if (node->children().empty()) {
      // If node has unexplored children, then
      bool expanded =
          node->expand(formula_evaluators, cs, contractor, branch_timer_guard,
                       eval_timer_guard, prune_timer_guard, config(), stat);

      if (expanded) {
        DREAL_LOG_INFO("X");
        MctsNode* child = node->select();
        wins = child->simulate(formula_evaluators, cs, contractor,
                               eval_timer_guard, prune_timer_guard, config(),
                               stat, rnd);
        DREAL_LOG_INFO("{}", wins);
      } else {
        wins = 1;
      }
      // child->backpropagate();
    } else {
      // Node is interior, and need to select child to recurse
      MctsNode* child = node->select();
      DREAL_LOG_INFO(".");
      wins =
          MctsBP(child, formula_evaluators, cs, contractor, branch_timer_guard,
                 eval_timer_guard, prune_timer_guard, stat, rnd);
    }
  } else {
    // Node is decided
    wins = 1;
    DREAL_LOG_INFO("{}", wins);
  }
  node->increment_visited();
  node->backpropagate(wins);
  return wins;
}

}  // namespace dreal
