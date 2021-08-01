# 戦略 jssst のログ出力を要約する
from collections import namedtuple
import re
import datetime as dt
import sys

Line = namedtuple('Line', ['line', 'time', 'message'])

def parseLine(line):
    m = re.match('(\S*) - (.*)', line)
    if m is None:
        print(f"# ignored:\t{line}", end='')
        return
    print(f"# parsed:\t{line}", end='')
    return Line(
        line=m.group(0),
        time=parseTime(m.group(1)),
        message=m.group(2)
    )

def parseTime(time):
    return dt.datetime.strptime(time, '%H:%M:%S.%f')

# (|Q|, |X|, |D|)
def parseSize(size):
    m = re.match('\((\d+),(\d+),(\d+),(\d+),(\d+),(\d+)\)', size)
    return (int(m.group(1)), int(m.group(2)), int(m.group(4)))

# (|Q|, |D|)
def parseSizePA(size):
    m = re.match('\((\d+),(\d+)\)', size)
    return (int(m.group(1)), int(m.group(2)))

def summarize(lines):
    parsed = [parseLine(line) for line in lines]
    class TimeRegistrar:
        def __init__(self):
            self.time = None
        def setTime(self, time):
            self.time = time
    time = TimeRegistrar()
    res = {}
    def registerTime(newTime, name):
        if time.time is not None:
            res[name] = (newTime - time.time) // dt.timedelta(microseconds=1000)
        time.setTime(newTime)
    assert(re.match('start checkSat\(\)', parsed[0].message) is not None)
    registerTime(parsed[0].time, '') # start checkSat()
    while re.match('composition done', parsed[0].message) is None:
        parsed = parsed[1:]
    res['size'] = parseSizePA(re.match('composition done: (.*)', parsed[0].message).group(1))
    registerTime(parsed[0].time, 'comp') # composition done
    registerTime(parsed[1].time, 'check') # checkSat() done
    # [un]sat
    # start getModel()
    if len(parsed) > 4:
        registerTime(parsed[4].time, 'model') # getModel() done
    return res

if __name__ == '__main__':
    lines = sys.stdin.readlines()
    summary = summarize([line for line in lines if line != ''])
    print(summary)
    # re.
