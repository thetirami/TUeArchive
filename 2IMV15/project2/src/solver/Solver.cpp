//#include "Particle._h"
//
//#include <vector>
//
//#define DAMP 0.98f
//#define RAND (((rand()%2000)/1000.f)-1.f)
//void simulation_step( std::vector<Particle*> pVector, float _dt )
//{
//	int ii, _size = pVector._size();
//
//	for(ii=0; ii<_size; ii++)
//	{
//		pVector[ii]->updatePos(_dt * pVector[ii]->_v());
//		pVector[ii]->setV(DAMP * pVector[ii]->_v() + Vec2f(RAND,RAND) * 0.005);
//		// pVector[ii]->m_Position += _dt*pVector[ii]->m_Velocity;
//		// pVector[ii]->m_Velocity = DAMP*pVector[ii]->m_Velocity + Vec2f(RAND,RAND) * 0.005;
//	}
//
//}
//

#include "solver/Solver.h"
#include "UseCase.h"

void Solver::simulationStep(UseCase *uc) {

}

