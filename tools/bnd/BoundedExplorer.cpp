#include "deep/BndExpl.hpp"
#include <chrono>
#include <thread>
#include <mutex>
#include <condition_variable>

using namespace ufo;
using namespace std;

std::chrono::duration<int, std::milli> timeout_wrapper(string & input_file, int & lower, int & upper){


  std::mutex m;
  std::condition_variable cv;
  std::chrono::duration<int, std::milli> duration;
  std::thread t([&cv, &input_file, &lower, &upper, &duration](){
    auto start = std::chrono::high_resolution_clock::now();
    unrollAndCheck(input_file, lower, upper);
    auto stop = std::chrono::high_resolution_clock::now();
    duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop-start);
    cv.notify_one();
  });

  t.detach();

  {
    std::unique_lock<std::mutex> l(m);
    if(cv.wait_for(l,std::chrono::seconds(60))==std::cv_status::timeout)
      throw std::runtime_error("Timeout");
  }

  return duration;

}

int main (int argc, char ** argv)
{
  if (argc == 1){
    outs() << "At least an input file should be given\n";
    return 0;
  }
/*
  int lower = 2;           //default
  int upper = 10000;       //default

  if (argc > 2) lower = max(2, atoi(argv[1]));
  if (argc > 3) upper = atoi(argv[2]);

  unrollAndCheck(string(argv[argc-1]), lower, upper);

  */
  int lower = 2;           //default
  int upper = 10000;       //default
  string input_file = string(argv[argc-1]);

  if (argc > 2) lower = max(2, atoi(argv[1]));
  if (argc > 3) upper = atoi(argv[2]);
  bool timeout = false;
  std::chrono::duration<int, std::milli> runtime;
  try{
    runtime = timeout_wrapper(input_file,lower,upper);
  }catch (std::runtime_error& e){
    timeout=true;
  }

  if(timeout)
    outs()<<"0:Timeout";
  else
    outs()<<runtime.count()<<"ms";



  return 0;
}
