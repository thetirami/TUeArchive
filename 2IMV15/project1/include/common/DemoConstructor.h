#include "UseCase.h"

class DemoConstructor {
private:
public:
    DemoConstructor() = default;
    static void DummyToy(UseCase* uc);
    static void Cloth2D(UseCase* uc);
    void AngularSpring(UseCase* uc);
    static void Hair(UseCase* uc);
};
