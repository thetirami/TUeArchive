//
// Created by xuanshu on 2022/05/26.
//

#include "solver/EulerSolver.h"
#include "eigen/Eigen/SparseCore"


EulerSolver::EulerSolver(EulerSolver::TYPE type) : _type(type) {

}

void EulerSolver::simulationStep(UseCase* uc) {
    switch (_type) {
        case EXPLICIT:
            explSolver(uc);
            break;
        case IMPLICIT:
            implSolver(uc);
            break;
        case SEMI:
            semiSolver(uc);
    }
}

void EulerSolver::explSolver(UseCase* uc) {
    Eigen::VectorXf oldState = uc->getState();
    Eigen::VectorXf stateDeriv = uc->aParticle();
    Eigen::VectorXf newState = oldState + uc->dt() * stateDeriv;
    if (uc->wall())
        newState = uc->wallCollision(newState);
    uc->setState(newState, uc->t() + uc->dt());
}

void EulerSolver::semiSolver(UseCase* uc) {
    Eigen::VectorXf oldState = uc->getState();
    Eigen::VectorXf stateDeriv = uc->aParticle();
    Eigen::VectorXf newState = oldState + uc->dt() * stateDeriv;
    uc->setState(newState, uc->t() + uc->dt());
    //Use new vectory
    for (int i = 0; i < newState.size(); i += 4) {
        newState[i + 0] = oldState[i + 0] + uc->dt() * newState[i + 2];
        newState[i + 1] = oldState[i + 1] + uc->dt() * newState[i + 3];
    }
    if (uc->wall())
        newState = uc->wallCollision(newState);
    uc->setState(newState, uc->t() + uc->dt());
}


void EulerSolver::implSolver(UseCase* uc) {
    Eigen::VectorXf oldState = uc->getState();
    uc->aParticle();
    // Fill mass matrix
    Eigen::SparseMatrix<float> M(uc->pDims()/2, uc->pDims()/2);

    std::vector<Eigen::Triplet<float>> MtripletList;
    MtripletList.reserve(uc->pDims()/2);
    for (int i = 0; i < uc->p().size() * 2; i += 2) {
        MtripletList.emplace_back(i+0, i+0, uc->p(i/2)->m());
        MtripletList.emplace_back(i+1, i+1, uc->p(i/2)->m());
    }
    M.setFromTriplets(MtripletList.begin(), MtripletList.end());

    // Fill jx and jy matrix based
    Eigen::SparseMatrix<float> jx(uc->pDims()/2, uc->pDims()/2);
    Eigen::MatrixXf jv(uc->pDims()/2, uc->pDims()/2);

    // Initialize empty map to compute jx
    auto jxm = std::map<int, std::map<int, float>>();
    unsigned long entries = 0;
    for (Force *f : uc->f()) {
        // Compute map for every force and update jxm appropriately
        auto fjx = f->dx();
        for (const auto &i1 : fjx) {
            for (const auto &i2 : i1.second) {
                if (jxm.count(i1.first) && jxm[i1.first].count(i2.first)) {
                    // i1 and i2 exist
                    // Hence, we update the already existing value
                    jxm[i1.first][i2.first] += i2.second;
                } else {
                    // No value yet exists, since i1 or i2 does not exist
                    // Hence we set a new value
                    jxm[i1.first][i2.first] = i2.second;
                    entries++;
                }
            }
        }
        if (f->p().size() == 2) {
            Eigen::MatrixXf fjv = f->dv();
            jv.block(f->p()[0]->ind() * 2, f->p()[1]->ind() * 2, fjv.cols(), fjv.rows()) = fjv;
            jv.block(f->p()[1]->ind() * 2, f->p()[0]->ind() * 2, fjv.cols(), fjv.rows()) = fjv;
        }
    }

    std::vector<Eigen::Triplet<float>> JxTripletList;
    JxTripletList.reserve(entries);
    for (const auto &i1 : jxm) {
        for (const auto &i2 : i1.second) {
            JxTripletList.emplace_back(i1.first, i2.first, i2.second);
        }
    }
    jx.setFromTriplets(JxTripletList.begin(), JxTripletList.end());

    // Get fold and vold
    Eigen::SparseVector<float> fold(uc->pDims()/2);
    Eigen::SparseVector<float> vold(uc->pDims()/2);

    for (int i = 0; i < uc->p().size(); i++) {
        vold.coeffRef(i * 2 + 0) = uc->p(i)->v(0);
        vold.coeffRef(i * 2 + 1) = uc->p(i)->v(1);
        fold.coeffRef(i * 2 + 0) = uc->p(i)->f(0);
        fold.coeffRef(i * 2 + 1) = uc->p(i)->f(1);
    }

    float h = uc->dt();
    // Compute A
    Eigen::SparseMatrix<float> A = M - h * h * jx; // - h * jv;
    Eigen::SparseVector<float> b = h * (fold + h * jx * vold);
    // Solve for dy
    Eigen::ConjugateGradient<Eigen::SparseMatrix<float>, Eigen::Lower | Eigen::Upper> cg;
    cg.compute(A);
    Eigen::SparseVector<float> dy = cg.solve(b);
    // Set new state
    Eigen::VectorXf newState(uc->pDims());
    for (int i = 0; i < dy.size(); i += 2) {
        int si = i * 2; // State index
        newState[si + 0] = oldState[si + 0] + (oldState[si + 2] + dy.coeff(i+0)) * h;
        newState[si + 1] = oldState[si + 1] + (oldState[si + 3] + dy.coeff(i+1)) * h;
        newState[si + 2] = oldState[si + 2] + dy.coeff(i+0);
        newState[si + 3] = oldState[si + 3] + dy.coeff(i+1);
    }
    if (uc->wall())
        newState = uc->wallCollision(newState);
    uc->setState(newState, uc->t()+uc->dt());
}



