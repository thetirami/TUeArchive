#include "solver/Solver.h"
#include "UseCase.h"

#include <cmath>


UseCase::UseCase(Solver* solver, Fluid* fluid) : _solver(solver), _fluid(fluid) {}
void UseCase::maintainConstraint(float ks, float kd) {
    if (_c.empty())
        return;
    int pDim = 2;
    int pUCSize = _p.size() * pDim;
    Eigen::MatrixXf M = Eigen::MatrixXf::Zero(pUCSize, pUCSize);
    Eigen::MatrixXf W = Eigen::MatrixXf::Zero(pUCSize, pUCSize);
    Eigen::VectorXf q = Eigen::VectorXf::Zero(pUCSize);
    Eigen::VectorXf qDot = Eigen::VectorXf::Zero(pUCSize);
    for (int i = 0; i < pUCSize; i += pDim) {
        Particle *p = _p[i/pDim];
        for (int j = 0; j < pDim; j++) {
            q[i+j] = p->f(j);
            qDot[i+j] = p->v(j);
            M(i+j, i+j) = p->m();
            W(i+j, i+j) = 1 / p->m();
        }
    }
    int cUCSize = _c.size();
    Eigen::VectorXf C = Eigen::VectorXf::Zero(cUCSize);
    Eigen::VectorXf CDot = Eigen::VectorXf::Zero(cUCSize);
    Eigen::MatrixXf J = Eigen::MatrixXf::Zero(cUCSize, pUCSize);
    Eigen::MatrixXf JDot = Eigen::MatrixXf::Zero(cUCSize, pUCSize);
    Eigen::MatrixXf Jt = Eigen::MatrixXf::Zero(pUCSize, cUCSize);
    for (int i = 0; i < cUCSize; i++) {
        Constraint *c = _c[i];
        C[i] = c->C();
        CDot[i] = c->legalV();
        std::vector<Eigen::Vector2f> jacobian = c->jacobian();
        std::vector<Eigen::Vector2f> jacobianDerivative = c->dJacobian();
        std::vector<Particle*> constraintsParticleVector = c->p();
        for (int j = 0; j < constraintsParticleVector.size(); j++) {
            int idx = constraintsParticleVector[j]->ind() * pDim;
            for (int k = 0; k < pDim; k++) {
                JDot(i, idx+k) = jacobianDerivative[j][k];
                J(i, idx+k) = jacobian[j][k];
                Jt(idx+k, i) = jacobian[j][k];
            }
        }
    }
    Eigen::MatrixXf JW = J * W, JWJt = JW * Jt;
    Eigen::VectorXf ksC = ks * C;
    Eigen::VectorXf kdCDot = kd * CDot;
    Eigen::VectorXf JDotqDot = JDot * qDot;
    Eigen::VectorXf JWQ = JW * q;
    Eigen::VectorXf b = -JDotqDot - JWQ - ksC - kdCDot;
    Eigen::ConjugateGradient<Eigen::MatrixXf, Eigen::Lower|Eigen::Upper> cg;
    cg.compute(JWJt);
    Eigen::VectorXf lambda = cg.solve(b);
    // Compute the constraint force Q hat
    Eigen::VectorXf QHat = Jt * lambda;
    for (int i = 0; i < _p.size(); i++) {
        Particle *p = _p[i];
        int idx = pDim * i;
        for (int j = 0; j < pDim; j++) {
            p->updateF(QHat[idx + j], j);
        }
    }
}

Eigen::VectorXf UseCase::getPState() {
    Eigen::VectorXf s(this->pDims());
    for (int i = 0; i < _p.size(); i++) {
        s[i * 4 + 0] = _p[i]->pos(0);
        s[i * 4 + 1] = _p[i]->pos(1);
        s[i * 4 + 2] = _fluid->getXVelocity(_p[i]->localGrid(128)[0], _p[i]->localGrid(128)[1]) * 50;
        s[i * 4 + 3] = _fluid->getXVelocity(_p[i]->localGrid(128)[0], _p[i]->localGrid(128)[1]) * 50;
    }
    return s;
}

Eigen::VectorXf UseCase::getRPState() {
    Eigen::VectorXf s(this->rpDims());
    for (int i = 0; i < _rp.size(); i++) {
        s[i * 8 + 0] = _rp[i]->massCenter()[0];
        s[i * 8 + 1] = _rp[i]->massCenter()[1];
        s[i * 8 + 2] = 0;
        s[i * 8 + 3] = _rp[i]->lm()[0];
        s[i * 8 + 4] = _rp[i]->lm()[1];
        s[i * 8 + 5] = _rp[i]->am();
        s[i * 8 + 6] = _rp[i]->m();
        s[i * 8 + 7] = _rp[i]->inertia();
    }
    return s;
}

void UseCase::setPState(Eigen::VectorXf s, float t) {
    for (int i = 0; i < _p.size(); i++) {
        _p[i]->setPos(s[i * 4 + 0], 0);
        _p[i]->setPos(s[i * 4 + 1], 1);
        _p[i]->setV(s[i * 4 + 2], 0);
        _p[i]->setV(s[i * 4 + 3], 1);
    }
    _t = t;
}

void UseCase::setRPState(Eigen::VectorXf s, float t) {
    for (int i = 0; i < _rp.size(); i++) {
        for (int k = 0; k < _rp[i]->boundBox().size(); ++k) {
            _rp[i]->updateBoundBox(-_rp[i]->massCenter(), k);
        }
        _rp[i]->setMassCenter(s[i * 8 + 0], s[i * 8 + 1]);
        _rp[i]->setAngle(_rp[i]->type() != RIGID ? 0.0f : s[i * 8 + 2]);
        _rp[i]->setLM(_rp[i]->type() == FIX ? 0.0f : s[i * 8 + 3], _rp[i]->type() == FIX ? 0.0f : s[i * 8 + 4]);
        _rp[i]->setAM(_rp[i]->type() != RIGID ? 0.0f : s[i * 8 + 5]);
        _rp[i]->setR(0, 0,  std::cos(_rp[i]->angle()));
        _rp[i]->setR(0, 1, -std::sin(_rp[i]->angle()));
        _rp[i]->setR(1, 0,  std::sin(_rp[i]->angle()));
        _rp[i]->setR(1, 1,  std::cos(_rp[i]->angle()));
        _rp[i]->setV(_rp[i]->type() == FIX ? Eigen::Vector2f(0.0f, 0.0f) : (_rp[i]->lm() / _rp[i]->m()));
        _rp[i]->setInertia(_rp[i]->m() * (pow(_rp[i]->dimension(), 2) + pow(_rp[i]->dimension(), 2)));
        _rp[i]->setOmega(_rp[i]->am() / (_rp[i]->inertia() + 0.00000000001));
        if (_rp[i]->omega() > 0.1) {
            _rp[i]->setOmega(0.1);
        }
        if (_rp[i]->omega() < -0.1) {
            _rp[i]->setOmega(-0.1);
        }
        for (int k = 0; k < _rp[i]->boundBox().size(); k++) {
            _rp[i]->setBoundBox(_rp[i]->r() * _rp[i]->boundBox(k) + _rp[i]->massCenter(), k);
        }
    }
    _t = t;
}

Eigen::VectorXf UseCase::dParticle() {
    Eigen::VectorXf dst(this->pDims());
    for (int i = 0; i < _p.size(); i++) {
        dst[i * 4 + 0] = _p[i]->v(0);
        dst[i * 4 + 1] = _p[i]->v(1);
        dst[i * 4 + 2] = _p[i]->f(0) / _p[i]->m();
        dst[i * 4 + 3] = _p[i]->f(1) / _p[i]->m();
    }
    return dst;
}

Eigen::VectorXf UseCase::dRParticle() {
    Eigen::VectorXf y(this->rpDims());
    for (int i = 0; i < _rp.size(); i++) {
        y[i * 8 + 0] = _rp[i]->v(0);
        y[i * 8 + 1] = _rp[i]->v(1);
        y[i * 8 + 2] = _rp[i]->omega();
        y[i * 8 + 3] = _rp[i]->f(0);
        y[i * 8 + 4] = _rp[i]->f(1);
        y[i * 8 + 5] = _rp[i]->torque();
        y[i * 8 + 6] = 0.0f;
        y[i * 8 + 7] = 0.0f;
    }
    return y;
}

void UseCase::simulationStep() {
    _solver->simulationStep(this);
}
