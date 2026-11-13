"""Observation-only adapter to the proved Lean kernel."""
import subprocess
from common import ROOT


class Kernel:
    def __init__(self,policy,errors):
        self.policy=1 if policy=='early' else 0
        self.process=subprocess.Popen(['lake','env','lean','--run','Bridge.lean'],cwd=ROOT,
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=errors,text=True,bufsize=1)
        if self.process.stdout.readline().strip()!='READY':
            self.close()
            raise RuntimeError('Lean kernel did not become ready')

    def decide(self,reserve_report,rate_report,delivered,carry):
        self.process.stdin.write(f'{self.policy} {reserve_report} {rate_report} {int(delivered)} {carry or 0}\n')
        self.process.stdin.flush()
        parts=self.process.stdout.readline().strip().split()
        if len(parts)!=5 or parts[0] not in ('wait','write','refuse'):
            raise RuntimeError('Invalid Lean response: '+repr(parts))
        return parts[0],*[int(x) for x in parts[1:]]

    def close(self):
        if self.process.poll() is None:
            self.process.stdin.close()
            try:
                self.process.wait(timeout=30)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=10)
        self.process.stdout.close()
        if self.process.returncode:
            raise RuntimeError('Lean kernel exited '+str(self.process.returncode))


