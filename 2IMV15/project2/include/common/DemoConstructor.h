#include "UseCase.h"
#include "Fluid.h"

class DemoConstructor {
private:
public:
    DemoConstructor() = default;
    void DummyToy(UseCase* uc);
    void FixedObject(UseCase* uc, Fluid* fluid);
    void MovingSolid(UseCase* uc, Fluid* fluid);
    void MovingRigid(UseCase* uc, Fluid* fluid);
    void Collision2R(UseCase* uc, Fluid* fluid);
    void Cloth2D(UseCase* uc);
};
